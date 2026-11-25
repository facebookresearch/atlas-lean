/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/MultiplicativeSheaf.lean`
(AxiomMath/Stacks, revision `c496df0d9beea9deaeabcea8492605f9a0a2313b`); the source file carries
no individual copyright or author notice.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Modifications: the associated sheaf on Mathlib's big étale site and its native cohomology
presheaf are used; the big/small field comparison is recorded in the interoperability
requests, not silently identified.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.GroupTheory.Torsion
public import MathlibExt.AlgebraicGeometry.BrauerCoefficients
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Category.Grp.AB

/-!
# Native geometric pullback of multiplicative cohomology

The units coefficient is the actual presheaf `U ↦ Γ(U,𝒪_U)ˣ`, written
additively. Its associated sheaf is used on the big étale site. Pullback is
the actual contravariant map of Mathlib's sheaf cohomology presheaf; a field
point is a scheme morphism `Spec K ⟶ X`. No evaluation homomorphism is supplied
as unconstrained data.

The comparison to Axiom's small étale field cohomology, and then to derived
Galois invariants and Tau's Brauer carrier, remains an explicit source adapter.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerEvaluation

open CategoryTheory CategoryTheory.Abelian Opposite

/-- Actual global units on schemes, with the additive convention for sheaves. -/
def unitsPresheaf : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    CommGrpCat.toAddCommGrp

/-- The associated multiplicative sheaf in the needed coefficient universe. -/
def gmSheaf : Sheaf Scheme.etaleTopology.{0} AddCommGrpCat.{1} :=
  (presheafToSheaf _ _).obj (unitsPresheaf ⋙ AddCommGrpCat.uliftFunctor.{1})

instance : IsGrothendieckAbelian.{1}
    (Sheaf Scheme.etaleTopology.{0} AddCommGrpCat.{1}) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
    Scheme.etaleTopology AddCommGrpCat.{1}

/-- The functor sending a scheme $X$ to the free abelian sheaf $\mathbb{Z}[h_X]$ on the big étale
site of schemes: the sheafification of the presheaf $T \mapsto \mathbb{Z}[\mathrm{Hom}(T, X)]$ of
free abelian groups on the morphisms $T \to X$. -/
def representedFreeSheaf :
    Scheme.{0} ⥤ Sheaf Scheme.etaleTopology.{0} AddCommGrpCat.{1} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
    (uliftFunctor.{1} ⋙ AddCommGrpCat.free) ⋙ presheafToSheaf _ _

/-- Actual étale `Gm` cohomology at a scheme. -/
abbrev GmH (X : Scheme.{0}) (n : ℕ) : AddCommGrpCat.{1} :=
  AddCommGrpCat.of (Ext (representedFreeSheaf.obj X) gmSheaf n)

abbrev GmH2 (X : Scheme.{0}) := GmH X 2

/-- Pullback by a scheme morphism is the native cohomology-presheaf map. -/
def pullback {X Y : Scheme.{0}} (f : X ⟶ Y) : GmH2 Y →+ GmH2 X :=
  { toFun a := (Ext.mk₀ (representedFreeSheaf.map f)).comp a (zero_add 2)
    map_zero' := by simp
    map_add' a b := by simp [Ext.comp_add] }

@[simp] theorem pullback_id (X : Scheme.{0}) :
    pullback (𝟙 X) = AddMonoidHom.id _ := by
  ext a
  simp [pullback, Ext.mk₀_id_comp]

theorem pullback_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  ext a
  simp only [pullback, AddMonoidHom.coe_mk, AddMonoidHom.coe_comp,
    Function.comp_apply, Functor.map_comp]
  exact (Ext.mk₀_comp_mk₀_assoc _ _ a).symm

/-- The cohomological Brauer subgroup is actual torsion in `H²(Gm)`. -/
abbrev Brauer (X : Scheme.{0}) := AddCommGroup.torsion (GmH2 X)

/-- Evaluation at an actual field-valued scheme point. Its endpoint is fixed
by that point's field, and its map is the actual geometric pullback. -/
def pointPullback (K : Type) [Field K] {X : Scheme.{0}}
    (p : Spec (.of K) ⟶ X) : GmH2 X →+ GmH2 (Spec (.of K)) := pullback p

theorem pointPullback_baseChange (K L : Type) [Field K] [Field L]
    (f : K →+* L) {X : Scheme.{0}} (p : Spec (.of K) ⟶ X) :
    pointPullback L (Spec.map (CommRingCat.ofHom f) ≫ p) =
      (pullback (Spec.map (CommRingCat.ofHom f))).comp (pointPullback K p) :=
  pullback_comp _ _

/-! ## Geometric Čech realization fixes the comparison's sign -/

open BrauerCoefficients
open scoped Simplicial

abbrev EtaleAb := Sheaf Scheme.etaleTopology.{0} AddCommGrpCat.{1}

/-- The actual lifted represented presheaf used by `representedFreeSheaf`. -/
def liftedRepresentable (T : Scheme.{0}) : Scheme.{0}ᵒᵖ ⥤ Type 1 :=
  yoneda.obj T ⋙ uliftFunctor.{1}

/-- The actual free abelian presheaf before its associated sheaf. -/
def freeRepresentablePresheaf (T : Scheme.{0}) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} :=
  liftedRepresentable T ⋙ AddCommGrpCat.free

/-- A units section maps to the associated units sheaf by its actual unit map. -/
def unitSection (T : Scheme.{0}) (s : unitsPresheaf.obj (op T)) :
    gmSheaf.obj.obj (op T) :=
  (toSheafify _ (unitsPresheaf ⋙ AddCommGrpCat.uliftFunctor.{1})).app (op T) (ULift.up s)

/-- The Yoneda morphism of an actual units section, with its literal restriction maps. -/
def unitSectionYoneda (T : Scheme.{0}) (s : unitsPresheaf.obj (op T)) :
    liftedRepresentable T ⟶ gmSheaf.obj ⋙ forget AddCommGrpCat.{1} where
  app U := TypeCat.ofHom fun h => (gmSheaf.obj.map h.down.op) (unitSection T s)
  naturality U V f := by
    ext h
    change (gmSheaf.obj.map (h.down.op ≫ f)) (unitSection T s) =
      (gmSheaf.obj.map f) ((gmSheaf.obj.map h.down.op) (unitSection T s))
    rw [Functor.map_comp]
    rfl

/-- The morphism from the actual represented free sheaf associated to a units section.
Both free-forgetful and sheafification adjunctions are fixed native adjunctions. -/
def unitSectionMap (T : Scheme.{0}) (s : unitsPresheaf.obj (op T)) :
    representedFreeSheaf.obj T ⟶ gmSheaf :=
  ((sheafificationAdjunction _ _).homEquiv (freeRepresentablePresheaf T) gmSheaf).symm
    (((AddCommGrpCat.adj.whiskerRight Scheme.{0}ᵒᵖ).homEquiv
      (liftedRepresentable T) gmSheaf.obj).symm (unitSectionYoneda T s))

/-- Degree-zero field units are literal represented-free-sheaf morphisms. -/
def fieldUnitZeroClass (K : Type) [Field K] (u : Kˣ) : GmH (Spec (.of K)) 0 :=
  Ext.mk₀ (unitSectionMap (Spec (.of K))
    (Additive.ofMul (Units.map (Scheme.ΓSpecIso (.of K)).inv.hom.toMonoidHom u)))

/-- Actual finite Galois étale charts inside the same separable closure as the coefficients. -/
structure GaloisCechChart (K : Type) [Field K] where
  E : IntermediateField K (SeparableClosure K)
  [finite : FiniteDimensional K E]
  [galois : IsGalois K E]
  [etale : Etale (Spec.map (CommRingCat.ofHom (algebraMap K E)))]

attribute [instance] GaloisCechChart.finite GaloisCechChart.galois GaloisCechChart.etale

variable {K : Type} [Field K]

/-- The cover is the actual spectrum map of the chart's finite Galois field extension. -/
def galoisCover (P : GaloisCechChart K) : Arrow Scheme.{0} :=
  Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap K P.E)))

/-- The actual `(n+1)`-fold scheme fibre product of the same cover. -/
def cechTerm (P : GaloisCechChart K) (n : ℕ) : Scheme.{0} :=
  (galoisCover P).cechNerve.obj (op ⦋n⦌)

/-- The free-sheaf simplicial object of the literal Čech nerve. -/
def freeCech (P : GaloisCechChart K) : SimplicialObject EtaleAb :=
  (galoisCover P).cechNerve ⋙ representedFreeSheaf

/-- The literal augmentation, including the actual spectrum map on every simplicial term. -/
def augmentedFreeCech (P : GaloisCechChart K) : SimplicialObject.Augmented EtaleAb :=
  (SimplicialObject.Augmented.whiskeringObj Scheme.{0} EtaleAb representedFreeSheaf).obj
    (galoisCover P).augmentedCechNerve

/-- The actual alternating Čech chain complex, embedded by `n ↦ -n`. -/
def geometricCechComplex (P : GaloisCechChart K) : CochainComplex EtaleAb ℤ :=
  ((AlgebraicTopology.alternatingFaceMapComplex EtaleAb).obj (augmentedFreeCech P).left).extend
    ComplexShape.embeddingDownNat

/-- The native Čech augmentation. Its degree-zero map is the actual cover augmentation,
so a negated augmentation is not an admissible replacement. -/
def geometricCechAugmentation (P : GaloisCechChart K) :
    geometricCechComplex P ⟶
      (CochainComplex.singleFunctor EtaleAb 0).obj (representedFreeSheaf.obj (Spec (.of K))) :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (augmentedFreeCech P))
    ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (representedFreeSheaf.obj (Spec (.of K))) 0 0 (by rfl)).hom

/-- The canonical degree-`-2` identification with the free sheaf of the actual triple product. -/
def cechDegreeTwoIso (P : GaloisCechChart K) :
    (geometricCechComplex P).X (-2) ≅ representedFreeSheaf.obj (cechTerm P 2) :=
  ((AlgebraicTopology.alternatingFaceMapComplex EtaleAb).obj (augmentedFreeCech P).left).extendXIso
    ComplexShape.embeddingDownNat (i := 2) (by rfl)

/-- Actual geometric points of the same Čech cover, using the three restricted automorphisms. -/
def sepAutomorphism (g : Field.absoluteGaloisGroup K) : Gal(SeparableClosure K/K) :=
  g.separableClosure

def cechGeometricPoint (P : GaloisCechChart K) (n : ℕ)
    (g : Fin (n + 1) → Field.absoluteGaloisGroup K) :
    Spec (.of (SeparableClosure K)) ⟶ cechTerm P n :=
  Limits.WidePullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))))
    (fun i => Spec.map (CommRingCat.ofHom
      ((sepAutomorphism (g i)).toRingHom.comp P.E.val.toRingHom))) (by
        intro i
        change Spec.map (CommRingCat.ofHom
          ((sepAutomorphism (g i)).toRingHom.comp P.E.val.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K P.E)) = _
        rw [← Spec.map_comp]
        congr 1
        ext a
        exact congrArg (fun x : SeparableClosure K => (x : AlgebraicClosure K))
          ((sepAutomorphism (g i)).commutes a))

/-- Literal evaluation of a units section at an actual `Ksep`-valued scheme point. -/
def unitPointValue {T : Scheme.{0}} (p : Spec (.of (SeparableClosure K)) ⟶ T)
    (s : unitsPresheaf.obj (op T)) : SepUnits K :=
  Additive.ofMul (Units.map
    ((Scheme.ΓSpecIso (.of (SeparableClosure K))).hom.hom.comp (Scheme.Γ.map p.op).hom)
      s.toMul)

/-- A realization of a native cocycle by an actual finite Galois Čech chart.
Its cochain is fixed by an actual units section, and that section is fixed
on every geometric triple point by the native homogeneous cocycle values. -/
structure GeometricCocycleRealization (K : Type) [Field K] (c : TwoCocycles K) where
  chart : GaloisCechChart K
  [augmentation_quasiIso : QuasiIso (geometricCechAugmentation chart)]
  unitsSection : unitsPresheaf.obj (op (cechTerm chart 2))
  cochain : geometricCechComplex chart ⟶ (CochainComplex.singleFunctor EtaleAb (-2)).obj gmSheaf
  cochain_component : cochain.f (-2) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-2) gmSheaf).hom =
    (cechDegreeTwoIso chart).hom ≫ unitSectionMap (cechTerm chart 2) unitsSection
  point_values : ∀ (g₀ g₁ g₂ : Field.absoluteGaloisGroup K),
    unitPointValue (cechGeometricPoint chart 2 ![g₀, g₁, g₂]) unitsSection =
      ((TopRep.homogeneousCochains (unitsRep K)).iCycles 2 c).val g₀ g₁ g₂

attribute [instance] GeometricCocycleRealization.augmentation_quasiIso

attribute [local instance] HasDerivedCategory.standard

/-- The geometric Čech class is an actual derived-category roof, not a freely supplied map.
The inverse is the inverse of the fixed Čech augmentation; the shift is the native degree two. -/
def geometricCechClass {c : TwoCocycles K} (R : GeometricCocycleRealization K c) :
    GmH2 (Spec (.of K)) :=
  Ext.homEquiv.symm
    ((asIso (DerivedCategory.Q.map (geometricCechAugmentation R.chart))).inv ≫
      DerivedCategory.Q.map R.cochain ≫
        ((DerivedCategory.singleFunctors EtaleAb).shiftIso 2 (-2) 0 (by decide)).inv.app gmSheaf)

end AlgebraicGeometry.BrauerEvaluation
