/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.WittLoopCorrespondences
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual relative and ramified Witt-loop test rings

The residue base is a specified ring k. Every test is an actual perfect
k-algebra R, including the zero algebra. For a specified W(k)-algebra B
and element pi, the integral ring is literally W(R) tensor W(k) B and
the rational ring is its native pi-localization. Every coefficient map
is the tensor of the actual Witt-vector map with identity on B.

For a mixed-characteristic local field these inputs are O_E, its actual
Cohen-Witt map and a uniformizer. The local-field dictionary and its
finite/complete hypotheses are separate geometric data. No local-field
property is asserted for an arbitrary B. Native group-scheme points,
positive loops and loops use these exact test schemes and maps.

Sources: Zhu, arXiv:1407.8519v3, Sections 0.1 and 1.4;
Fargues--Scholze, arXiv:2102.13459v4, Section I.2.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RelativeWittLoopTests

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]

/-- Actual perfect k-algebras retain all scalar maps and include the zero ring. -/
abbrev PerfectAlgebra :=
  (show ObjectProperty (CommAlgCat.{0} k) from
    fun R ↦ (p : R) = 0 ∧ Function.Bijective (fun x : R ↦ x ^ p)).FullSubcategory

/-- The actual Witt scalar map on each residue test ring. -/
def wittScalars (R : PerfectAlgebra p k) : WittVector p k →+* WittVector p R.obj :=
  WittVector.map (algebraMap k R.obj)

/-- The displayed algebra structure uses precisely this scalar map. -/
@[instance_reducible]
def wittAlgebra (R : PerfectAlgebra p k) :
    Algebra (WittVector p k) (WittVector p R.obj) :=
  (wittScalars p k R).toAlgebra

attribute [local instance] wittAlgebra

variable (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)

/-- The actual base-changed Witt ring, before uniformizer inversion. -/
abbrev Integral (R : PerfectAlgebra p k) : Type :=
  WittVector p R.obj ⊗[WittVector p k] B

instance integralCommRing (R : PerfectAlgebra p k) : CommRing (Integral p k B R) := by
  exact inferInstanceAs (CommRing (WittVector p R.obj ⊗[WittVector p k] B))

/-- Original coefficients embed by the native second tensor factor. -/
def coefficient (R : PerfectAlgebra p k) : B →+* Integral p k B R := by
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- The actual pure tensor, retaining both original coefficient factors. -/
def tensor (R : PerfectAlgebra p k) (w : WittVector p R.obj) (b : B) :
    Integral p k B R := w ⊗ₜ b

/-- The actual rational ring is localization at the image of the specified uniformizer. -/
abbrev Rational (R : PerfectAlgebra p k) :=
  Localization.Away (coefficient p k B R pi)

/-- The actual scalar-compatible Witt algebra map induced by a test morphism. -/
def wittMap {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    WittVector p R.obj →ₐ[WittVector p k] WittVector p S.obj := by
  refine { __ := WittVector.map f.hom.hom.toRingHom, commutes' := ?_ }
  intro a
  change WittVector.map f.hom.hom.toRingHom
    (WittVector.map (algebraMap k R.obj) a) = WittVector.map (algebraMap k S.obj) a
  ext n
  change f.hom.hom (algebraMap k R.obj (a.coeff n)) =
    algebraMap k S.obj (a.coeff n)
  exact f.hom.hom.commutes _

/-- Tensor the actual Witt map with the unchanged original coefficient ring. -/
def integralMap {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    Integral p k B R →+* Integral p k B S := by
  exact (Algebra.TensorProduct.map (wittMap p k f) (AlgHom.id (WittVector p k) B)).toRingHom

/-- Coefficients are fixed on every element of B. -/
theorem integralMap_coefficient {R S : PerfectAlgebra p k} (f : R ⟶ S) (b : B) :
    integralMap p k B f (coefficient p k B R b) = coefficient p k B S b := by
  change (Algebra.TensorProduct.map (wittMap p k f) (AlgHom.id (WittVector p k) B))
    (1 ⊗ₜ b) = 1 ⊗ₜ b
  simp

/-- The native localized map retains that same exact coefficient square. -/
def rationalMap {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    Rational p k B pi R →+* Rational p k B pi S :=
  Localization.awayLift
    ((algebraMap _ _).comp (integralMap p k B f))
    (coefficient p k B R pi) (by
      rw [RingHom.comp_apply, integralMap_coefficient]
      exact IsLocalization.Away.algebraMap_isUnit
        (S := Rational p k B pi S) (coefficient p k B S pi))

/-- Every localized coordinate retains the actual underlying tensor map. -/
theorem rationalMap_unit {R S : PerfectAlgebra p k} (f : R ⟶ S)
    (a : Integral p k B R) :
    rationalMap p k B pi f (algebraMap _ _ a) =
      algebraMap _ _ (integralMap p k B f a) := by
  simp only [rationalMap, Localization.awayLift, IsLocalization.Away.lift_eq,
    RingHom.comp_apply]

/-- Native tensor functoriality retains the identity Witt map. -/
theorem integralMap_id (R : PerfectAlgebra p k) :
    integralMap p k B (𝟙 R) = RingHom.id (Integral p k B R) := by
  apply Algebra.TensorProduct.ringHom_ext
  · ext a
    change WittVector.map (RingHom.id R.obj) a ⊗ₜ (1 : B) = a ⊗ₜ (1 : B)
    rw [WittVector.map_id]
    rfl
  · ext b
    exact integralMap_coefficient p k B (𝟙 R) b

/-- Native tensor functoriality retains every actual composed Witt coefficient map. -/
theorem integralMap_comp {R S T : PerfectAlgebra p k} (f : R ⟶ S) (g : S ⟶ T) :
    integralMap p k B (f ≫ g) =
      (integralMap p k B g).comp (integralMap p k B f) := by
  apply Algebra.TensorProduct.ringHom_ext
  · ext a
    change WittVector.map (g.hom.hom.toRingHom.comp f.hom.hom.toRingHom) a ⊗ₜ (1 : B) =
      WittVector.map g.hom.hom.toRingHom (WittVector.map f.hom.hom.toRingHom a) ⊗ₜ (1 : B)
    congr 1
  · ext b
    change integralMap p k B (f ≫ g) (coefficient p k B R b) =
      integralMap p k B g (integralMap p k B f (coefficient p k B R b))
    simp only [integralMap_coefficient]

/-- Uniformizer-localization retains the native identity map. -/
theorem rationalMap_id (R : PerfectAlgebra p k) :
    rationalMap p k B pi (𝟙 R) = RingHom.id (Rational p k B pi R) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coefficient p k B R pi))
  apply RingHom.ext
  intro a
  change rationalMap p k B pi (𝟙 R) (algebraMap _ _ a) = algebraMap _ _ a
  rw [rationalMap_unit, integralMap_id]
  rfl

/-- Uniformizer-localization retains composition of the actual tensor maps. -/
theorem rationalMap_comp {R S T : PerfectAlgebra p k} (f : R ⟶ S) (g : S ⟶ T) :
    rationalMap p k B pi (f ≫ g) =
      (rationalMap p k B pi g).comp (rationalMap p k B pi f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coefficient p k B R pi))
  apply RingHom.ext
  intro a
  change rationalMap p k B pi (f ≫ g) (algebraMap _ _ a) =
    rationalMap p k B pi g (rationalMap p k B pi f (algebraMap _ _ a))
  rw [rationalMap_unit, rationalMap_unit, rationalMap_unit]
  exact congrArg (algebraMap _ _) (RingHom.congr_fun (integralMap_comp p k B f g) a)

/-- The original B-valued affine test of the ramified Witt ring. -/
def integralTest (R : PerfectAlgebra p k) : Over (Spec (.of B)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (coefficient p k B R)))

/-- The original B-valued affine test after actual uniformizer inversion. -/
def rationalTest (R : PerfectAlgebra p k) : Over (Spec (.of B)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap (Integral p k B R) (Rational p k B pi R)).comp
      (coefficient p k B R))))

/-- Native contravariant scheme map on the actual tensor rings. -/
def integralTestMap {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    integralTest p k B S ⟶ integralTest p k B R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (integralMap p k B f))) (by
    change Spec.map (CommRingCat.ofHom (integralMap p k B f)) ≫
      Spec.map (CommRingCat.ofHom (coefficient p k B R)) =
        Spec.map (CommRingCat.ofHom (coefficient p k B S))
    rw [← Spec.map_comp]
    congr 1
    ext b
    exact integralMap_coefficient p k B f b)

/-- Native contravariant scheme map on the actual localized tensor rings. -/
def rationalTestMap {R S : PerfectAlgebra p k} (f : R ⟶ S) :
    rationalTest p k B pi S ⟶ rationalTest p k B pi R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (rationalMap p k B pi f))) (by
    change Spec.map (CommRingCat.ofHom (rationalMap p k B pi f)) ≫
      Spec.map (CommRingCat.ofHom ((algebraMap
        (Integral p k B R) (Rational p k B pi R)).comp (coefficient p k B R))) =
      Spec.map (CommRingCat.ofHom ((algebraMap
        (Integral p k B S) (Rational p k B pi S)).comp (coefficient p k B S)))
    rw [← Spec.map_comp]
    congr 1
    ext b
    change rationalMap p k B pi f (algebraMap _ _ (coefficient p k B R b)) =
      algebraMap _ _ (coefficient p k B S b)
    rw [rationalMap_unit, integralMap_coefficient])

/-- The integral test functor uses every actual relative Witt-ring morphism. -/
def integralTests : (PerfectAlgebra p k)ᵒᵖ ⥤ Over (Spec (.of B)) where
  obj R := integralTest p k B R.unop
  map f := integralTestMap p k B f.unop
  map_id R := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (integralMap p k B (𝟙 R.unop))) = 𝟙 _
    rw [integralMap_id]
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (integralMap p k B (f ≫ g).unop)) =
      Spec.map (CommRingCat.ofHom (integralMap p k B f.unop)) ≫
        Spec.map (CommRingCat.ofHom (integralMap p k B g.unop))
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (integralMap p k B (g.unop ≫ f.unop))) =
      Spec.map (CommRingCat.ofHom ((integralMap p k B f.unop).comp
        (integralMap p k B g.unop)))
    exact congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q))
      (integralMap_comp p k B g.unop f.unop)

/-- The rational test functor uses every actual uniformizer-localized morphism. -/
def rationalTests : (PerfectAlgebra p k)ᵒᵖ ⥤ Over (Spec (.of B)) where
  obj R := rationalTest p k B pi R.unop
  map f := rationalTestMap p k B pi f.unop
  map_id R := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (rationalMap p k B pi (𝟙 R.unop))) = 𝟙 _
    rw [rationalMap_id]
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (rationalMap p k B pi (f ≫ g).unop)) =
      Spec.map (CommRingCat.ofHom (rationalMap p k B pi f.unop)) ≫
        Spec.map (CommRingCat.ofHom (rationalMap p k B pi g.unop))
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (rationalMap p k B pi (g.unop ≫ f.unop))) =
      Spec.map (CommRingCat.ofHom ((rationalMap p k B pi f.unop).comp
        (rationalMap p k B pi g.unop)))
    exact congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q))
      (rationalMap_comp p k B pi g.unop f.unop)

/-- Actual localization on the represented affine tests. -/
def localization (R : PerfectAlgebra p k) :
    rationalTest p k B pi R ⟶ integralTest p k B R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap _ _))) (by
    change Spec.map (CommRingCat.ofHom (algebraMap
      (Integral p k B R) (Rational p k B pi R))) ≫
      Spec.map (CommRingCat.ofHom (coefficient p k B R)) =
        Spec.map (CommRingCat.ofHom ((algebraMap _ _).comp (coefficient p k B R)))
    rw [← Spec.map_comp]
    rfl)

/-- The entire native localization transformation fixes every original scalar. -/
def localizations : rationalTests p k B pi ⟶ integralTests p k B where
  app R := localization p k B pi R.unop
  naturality R S f := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (rationalMap p k B pi f.unop)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ _)) =
      Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫
        Spec.map (CommRingCat.ofHom (integralMap p k B f.unop))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change rationalMap p k B pi f.unop (algebraMap _ _ a) =
      algebraMap _ _ (integralMap p k B f.unop a)
    exact rationalMap_unit p k B pi f.unop a

variable (G : Over (Spec (.of B))) [GrpObj G]

/-- Actual group-scheme points of every relative integral Witt test ring. -/
def positiveLoops : PerfectAlgebra p k ⥤ GrpCat.{0} :=
  (integralTests p k B).rightOp ⋙ yonedaGrpObj G

/-- Actual group-scheme points of every uniformizer-localized Witt test ring. -/
def loops : PerfectAlgebra p k ⥤ GrpCat.{0} :=
  (rationalTests p k B pi).rightOp ⋙ yonedaGrpObj G

/-- The actual positive-loop homomorphism, with all scalar restrictions fixed. -/
def positiveToLoop : positiveLoops p k B G ⟶ loops p k B pi G :=
  Functor.whiskerRight (NatTrans.rightOp (localizations p k B pi)) (yonedaGrpObj G)

/-- The fpqc basis uses actual finite jointly faithfully flat families of perfect residue
algebras, that is, families whose product map is faithfully flat. Finite families, including the
empty family covering the zero algebra, make sheaves preserve finite products, as Zhu,
arXiv:1407.8519v3, Appendix A.1.1 requires in addition to the faithfully flat equaliser
condition. -/
def fpqcPrecoverage : Precoverage (PerfectAlgebra p k)ᵒᵖ where
  coverings R := {s | ∃ (J : Type) (_ : Finite J) (S : J → PerfectAlgebra p k)
    (f : ∀ i, R.unop ⟶ S i),
    (RingHom.pi fun i ↦ (f i).hom.hom.toRingHom).FaithfullyFlat ∧
      s = Presieve.ofArrows (fun i ↦ Opposite.op (S i)) fun i ↦ (f i).op}

/-- The native fpqc topology on all actual residue tests. -/
def fpqcTopology : GrothendieckTopology (PerfectAlgebra p k)ᵒᵖ :=
  (fpqcPrecoverage p k).toGrothendieck

end MathlibExt.AlgebraicGeometry.RelativeWittLoopTests
