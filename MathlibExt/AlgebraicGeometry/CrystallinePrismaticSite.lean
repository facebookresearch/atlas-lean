/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), `AlgebraicGeometry.hasSheafify_moduleCat`:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: the site is specialized to the crystalline prisms.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import MathlibExt.RingTheory.DeltaRing

/-!
# The actual crystalline prismatic site over (Z_p, (p))

An object is a p-torsion-free, p-complete δ-Z_p-algebra B and an actual
map `Spec(B/p) → X`. This is the crystalline-prism slice of the usual
prismatic site: rigidity of prism morphisms forces the ideal to be (p).
The δ-Frobenius fixes the actual structural Z_p scalars.

Morphisms are δ-algebra homomorphisms, in the geometric opposite
direction, respecting the displayed scheme map. The topology is the
smallest Grothendieck topology containing actual p-completely faithfully
flat covers. In this p-torsion-free complete scope these are specified by
faithful flatness on every finite p-power quotient.

The structure presheaf has the actual ring B as its underlying Z_p-module.
Its actual sheafification and the δ-Frobenius morphism are constructed.
No prismatic complex, period action or abstract cohomology is supplied.

Reference: Bhatt–Scholze, *Prisms and prismatic cohomology*, Example 3.3,
Lemma 3.5, and Definition 4.1, https://arxiv.org/abs/1905.08229.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CrystallinePrismaticSite

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.RingTheory

variable (p : ℕ) [Fact p.Prime]

/-- Identity on Z_p is the actual Frobenius lift of its prime-field residue. -/
theorem baseFrobenius_divisible (x : PadicInt p) :
    (p : PadicInt p) ∣ x - x ^ p := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow]
  have h : (PadicInt.toZMod x) ^ p = PadicInt.toZMod x := by
    simp
  exact sub_eq_zero.mpr h.symm

/-- The standard crystalline prism has its constructed δ-structure. -/
instance baseDelta : DeltaRing p (PadicInt p) :=
  DeltaRing.ofFrobeniusLift
    (isRegular_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    (RingHom.id _) (baseFrobenius_divisible p)

/-- Its actual prism Frobenius is the identity. -/
theorem baseFrobenius : DeltaRing.frobenius p (PadicInt p) = RingHom.id _ :=
  DeltaRing.frobenius_ofFrobeniusLift _ _ _

abbrev PrimeFieldScheme := Over (Spec (CommRingCat.of.{0} (ZMod p)))

/-- The actual finite p-power ideal. -/
def powerIdeal (B : Type) [CommRing B] (n : ℕ) : Ideal B :=
  Ideal.span {((p : B) ^ n)}

abbrev Reduction (B : Type) [CommRing B] (n : ℕ) :=
  B ⧸ powerIdeal p B n

/-- The actual base ring is complete for the displayed prism ideal. -/
theorem baseComplete : IsAdicComplete (powerIdeal p (PadicInt p) 1)
    (PadicInt p) := by
  change IsAdicComplete (Ideal.span {(p : PadicInt p) ^ 1}) (PadicInt p)
  rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

/-- The canonical prime-field map into the actual p-reduction. -/
def residueScalars (B : Type) [CommRing B] :
    ZMod p →+* Reduction p B 1 :=
  ZMod.castHom (by
    apply ringChar.dvd
    change Ideal.Quotient.mk (powerIdeal p B 1) (p : B) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)) _

variable (X : PrimeFieldScheme p)

/-- Actual δ-ring lifts and their maps to the given scheme. -/
structure Obj where
  ring : CommRingCat.{0}
  [algebra : Algebra (PadicInt p) ring]
  [delta : DeltaRing p ring]
  regular : IsRegular (p : ring)
  [complete : IsAdicComplete (powerIdeal p ring 1) ring]
  frobenius_base : ∀ a : PadicInt p,
    DeltaRing.frobenius p ring (algebraMap (PadicInt p) ring a) =
      algebraMap (PadicInt p) ring a
  point : Spec (CommRingCat.of (Reduction p ring 1)) ⟶ X.left
  point_base : point ≫ X.hom =
    Spec.map (CommRingCat.ofHom (residueScalars p ring))

attribute [instance] Obj.algebra Obj.delta Obj.complete

/-- The fixed structural Frobenius makes the base map an actual δ-map. -/
theorem Obj.delta_base (P : Obj p X) (a : PadicInt p) :
    DeltaRing.delta p (algebraMap (PadicInt p) P.ring a) =
      algebraMap (PadicInt p) P.ring (DeltaRing.delta p a) := by
  apply P.regular.left
  have h₁ := P.frobenius_base a
  have h₂ := congrArg (algebraMap (PadicInt p) P.ring)
    (DFunLike.congr_fun (baseFrobenius p) a)
  simp only [DeltaRing.frobenius_apply, map_add, map_pow, map_mul,
    map_natCast, RingHom.id_apply] at h₁ h₂
  exact add_left_cancel (h₁.trans h₂.symm)

/-- A concrete nonzero crystalline prism over the actual prime-field point. -/
def baseObject : Obj p (Over.mk (𝟙 (Spec (CommRingCat.of (ZMod p))))) where
  ring := CommRingCat.of (PadicInt p)
  algebra := inferInstance
  delta := baseDelta p
  regular := isRegular_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  complete := baseComplete p
  frobenius_base a := by
    change DeltaRing.frobenius p (PadicInt p) a = a
    rw [baseFrobenius]
    rfl
  point := Spec.map (CommRingCat.ofHom (residueScalars p (PadicInt p)))
  point_base := by simp

/-- The actual quotient map induced by an algebra homomorphism. -/
def reductionMap {B C : Type} [CommRing B] [CommRing C]
    [Algebra (PadicInt p) B] [Algebra (PadicInt p) C]
    (f : B →ₐ[PadicInt p] C) (n : ℕ) :
    Reduction p B n →+* Reduction p C n :=
  Ideal.quotientMap (powerIdeal p C n) f.toRingHom (by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change f ((p : B) ^ n) ∈ powerIdeal p C n
    rw [map_pow, map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp]
theorem reductionMap_id (B : Type) [CommRing B]
    [Algebra (PadicInt p) B] (n : ℕ) :
    reductionMap p (AlgHom.id (PadicInt p) B) n =
      RingHom.id (Reduction p B n) := by
  ext x
  simp [reductionMap]

theorem reductionMap_comp {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] [Algebra (PadicInt p) A] [Algebra (PadicInt p) B]
    [Algebra (PadicInt p) C] (f : B →ₐ[PadicInt p] C)
    (g : A →ₐ[PadicInt p] B) (n : ℕ) :
    reductionMap p (f.comp g) n =
      (reductionMap p f n).comp (reductionMap p g n) := by
  ext x
  simp [reductionMap]

variable {p X}

@[ext]
structure Hom (P Q : Obj p X) where
  map : Q.ring →ₐ[PadicInt p] P.ring
  delta_compat : ∀ a : Q.ring,
    map (DeltaRing.delta p a) = DeltaRing.delta p (map a)
  point_compat :
    Spec.map (CommRingCat.ofHom (reductionMap p map 1)) ≫ Q.point = P.point

instance : Category (Obj p X) where
  Hom := Hom
  id P :=
    { map := AlgHom.id _ _
      delta_compat := fun _ => rfl
      point_compat := by simp }
  comp f g :=
    { map := f.map.comp g.map
      delta_compat := by
        intro a
        change f.map (g.map (DeltaRing.delta p a)) =
          DeltaRing.delta p (f.map (g.map a))
        rw [g.delta_compat, f.delta_compat]
      point_compat := by
        rw [reductionMap_comp]
        change Spec.map (CommRingCat.ofHom (reductionMap p g.map 1) ≫
            CommRingCat.ofHom (reductionMap p f.map 1)) ≫ _ = _
        rw [Spec.map_comp, Category.assoc, g.point_compat, f.point_compat] }

variable (p X)

/-- The actual p-completely faithfully flat covering condition. -/
def IsCover {P Q : Obj p X} (f : P ⟶ Q) : Prop :=
  ∀ n : ℕ, 0 < n →
    letI := (reductionMap p f.map n).toAlgebra
    Module.FaithfullyFlat (Reduction p Q.ring n) (Reduction p P.ring n)

/-- The topology is generated by these actual flat single-map covers. -/
def topology : GrothendieckTopology (Obj p X) :=
  sInf {J | ∀ (P Q : Obj p X) (f : P ⟶ Q), IsCover p X f →
    Sieve.ofArrows (fun _ : Unit => P) (fun _ => f) ∈ J Q}

/-- Each specified covering map generates a covering sieve. -/
theorem cover_mem {P Q : Obj p X} (f : P ⟶ Q) (hf : IsCover p X f) :
    Sieve.ofArrows (fun _ : Unit => P) (fun _ => f) ∈ topology p X Q := by
  rw [topology, GrothendieckTopology.mem_sInf]
  intro J hJ
  exact hJ P Q f hf

/-- Actual module sheafification exists in a universe containing the site. -/
instance moduleSheafify :
    HasSheafify (topology p X) (ModuleCat.{1} (PadicInt p)) := by
  let : HasLimits (ModuleCat.{1} (PadicInt p)) :=
    ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}
  let : PreservesColimitsOfSize.{1, 1}
      (forget₂ (ModuleCat.{1} (PadicInt p)) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} (PadicInt p)
  let : PreservesFilteredColimits (forget (ModuleCat.{1} (PadicInt p))) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (ModuleCat.{1} (PadicInt p)) AddCommGrpCat.{1})
      (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1}
      (forget (ModuleCat.{1} (PadicInt p))) := inferInstance
  infer_instance

/-- The structure presheaf consists of the actual δ-ring modules. -/
def structurePresheaf : (Obj p X)ᵒᵖ ⥤ ModuleCat.{1} (PadicInt p) where
  obj U := ModuleCat.of _ (ULift.{1} U.unop.ring)
  map f := ModuleCat.ofHom
    { toFun x := ULift.up (f.unop.map x.down)
      map_add' x y := ULift.ext (map_add f.unop.map x.down y.down)
      map_smul' r x := ULift.ext (f.unop.map.toLinearMap.map_smul r x.down) }
  map_id U := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- Its actual module sheafification is the structural sheaf. -/
def structureSheaf : Sheaf (topology p X) (ModuleCat.{1} (PadicInt p)) :=
  (presheafToSheaf (topology p X) (ModuleCat.{1} (PadicInt p))).obj
    (structurePresheaf p X)

/-- The native δ-Frobenius is linear over the fixed base Frobenius. -/
def frobeniusLinear (P : Obj p X) : P.ring →ₗ[PadicInt p] P.ring where
  toFun := DeltaRing.frobenius p P.ring
  map_add' := map_add _
  map_smul' r x := by
    rw [Algebra.smul_def, map_mul, P.frobenius_base, Algebra.smul_def]
    rfl

/-- Lift that actual linear map only to reconcile the site universe. -/
def liftedFrobenius (P : Obj p X) :
    ULift.{1} P.ring →ₗ[PadicInt p] ULift.{1} P.ring :=
  (ULift.moduleEquiv : ULift.{1} P.ring ≃ₗ[PadicInt p] P.ring)
    |>.symm.toLinearMap.comp
    ((frobeniusLinear p X P).comp
      (ULift.moduleEquiv : ULift.{1} P.ring ≃ₗ[PadicInt p] P.ring).toLinearMap)

/-- Frobenius is the native δ-ring lift on every actual structure ring. -/
def frobeniusPresheaf : structurePresheaf p X ⟶ structurePresheaf p X where
  app U := ModuleCat.ofHom (liftedFrobenius p X U.unop)
  naturality {U V} f := by
    ext x
    apply ULift.ext
    change DeltaRing.frobenius p V.unop.ring (f.unop.map x.down) =
      f.unop.map (DeltaRing.frobenius p U.unop.ring x.down)
    simp only [DeltaRing.frobenius_apply, map_add, map_pow, map_mul,
      map_natCast, f.unop.delta_compat]

/-- The structural sheaf Frobenius is the actual sheafified morphism. -/
def frobeniusSheaf : structureSheaf p X ⟶ structureSheaf p X :=
  (presheafToSheaf (topology p X) (ModuleCat.{1} (PadicInt p))).map
    (frobeniusPresheaf p X)

end MathlibExt.AlgebraicGeometry.CrystallinePrismaticSite
