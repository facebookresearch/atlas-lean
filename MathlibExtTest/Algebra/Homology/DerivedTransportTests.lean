/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.ChainComplex.NativeShift
import MathlibExt.Algebra.Homology.HomologicalComplex.SplitHomology
import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingFunctorTransport
import MathlibExt.Algebra.Category.ModuleCat.RelativeResolutionTensorHomology
import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Data.ZMod.Basic
meta import Lean.Elab.Tactic.Omega

/-!
# Tests for shifts, split complexes and relative transport

Odd chain shifts negate the differential and move its source indices. Two
splittings of a nonzero loop distinguish reflexive and square-zero normalization.
An integer-indexed complex with multiplication by two as its only nonzero edge
has projective outgoing images and a nonzero modulo-two homology class, but no
splitting. Tensor comparisons compute the map over multiplication by two.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

namespace MathlibExtTest.Algebra.Homology.DerivedTransport

abbrev V := ModuleCat.of ℤ (ℤ × ℤ)
abbrev Z := ModuleCat.of ℤ ℤ

/-- The square-zero map `(x,y) ↦ (y,0)`. -/
def d : V ⟶ V := ModuleCat.ofHom
  ((LinearMap.inl ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ ℤ))

/-- Its generalized inverse `(x,y) ↦ (0,x)`. -/
def h : V ⟶ V := ModuleCat.ofHom
  ((LinearMap.inr ℤ ℤ ℤ).comp (LinearMap.fst ℤ ℤ ℤ))

/-- A loop complex with a nonzero differential. -/
def loop : HomologicalComplex (ModuleCat ℤ) (ComplexShape.refl Unit) where
  X _ := V
  d _ _ := d
  shape _ _ hn := False.elim (hn (Subsingleton.elim _ _))
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, y⟩
    rfl

/-- Explicit inverse components for the loop differential. -/
def loopSplit : Splitting loop where
  hom _ _ := h
  zero _ _ hn := False.elim (hn (Subsingleton.elim _ _))
  d_h_d _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, y⟩
    rfl

/-- The example differential is nonzero. -/
example : d.hom (0, 1) = (1, 0) := rfl

/-- Normalization satisfies the generalized-inverse relation on nonzero data. -/
example : loopSplit.normalize.hom () () ≫ d ≫ loopSplit.normalize.hom () () =
    loopSplit.normalize.hom () () :=
  loopSplit.normalize_h_d_h () ()

/-- Consecutive normalized components vanish even on a loop shape. -/
example : loopSplit.normalize.hom () () ≫ loopSplit.normalize.hom () () = 0 :=
  loopSplit.normalize_hom_comp_hom () () ()

/-- The homology comparison retains its negative normalized inverse homotopy. -/
example : loopSplit.homotopyEquivHomology.homotopyHomInvId.hom () () =
    -loopSplit.normalize.hom () () :=
  loopSplit.homotopyEquivHomology_homotopyHomInvId_hom () ()

/-- Additive transport of this splitting commutes with normalization. -/
example : (loopSplit.map (𝟭 (ModuleCat ℤ))).normalize =
    loopSplit.normalize.map (𝟭 (ModuleCat ℤ)) :=
  loopSplit.map_normalize (𝟭 (ModuleCat ℤ))

section IntegerShift

variable (K : ChainComplex (ModuleCat ℤ) ℤ)

/-- An odd negative shift has the negative differential in degrees three and two. -/
example : ((ChainComplex.nativeShift (ModuleCat ℤ) (-1)).obj K).d 2 1 = -K.d 3 2 := by
  simp [ChainComplex.nativeShift_obj_d]

/-- Morphism transport changes the index without adding a scalar sign. -/
example (f : K ⟶ K) :
    ((ChainComplex.nativeShift (ModuleCat ℤ) (-1)).map f).f 2 = f.f 3 := by
  simp [ChainComplex.nativeShift_map_f]

/-- Native shift additivity is synthesized for the module category. -/
example : (ChainComplex.nativeShift (ModuleCat ℤ) 1).Additive := inferInstance

end IntegerShift

/-- Tensor transport is additive for a nonzero fixed coefficient module. -/
example : (ModuleCat.relativeTensorFunctor (R := ℤ) V).Additive := inferInstance

/-- Identity is relatively projective on the nonzero module, without absolute projectivity assumptions. -/
example : (𝟭 (ModuleCat ℤ)).IsRelativeProjective V :=
  (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).isRelativeProjective_obj V

/-- The first projection is split by its canonical inclusion. -/
def firstSplit : SplitEpi ((𝟭 (ModuleCat ℤ)).map
    (ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ) : V ⟶ Z)) where
  section_ := ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The adjoint lift factors a nonzero scalar map through the split projection. -/
example :
    (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).liftOfSplitEpi
        (ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)) firstSplit
        (ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) : Z ⟶ Z) ≫
      ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ) =
        (ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) : Z ⟶ Z) :=
  (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).liftOfSplitEpi_comp _ _ _

section NormalizationCounterexamples

private def swap : V ⟶ V :=
  ModuleCat.ofHom ((LinearMap.snd ℤ ℤ ℤ).prod (LinearMap.fst ℤ ℤ ℤ))

private def swapSplit : Splitting loop where
  hom _ _ := swap
  zero _ _ hn := False.elim (hn (Subsingleton.elim _ _))
  d_h_d _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    rfl

/-- Swap has a nonzero component killed by both normalization constructions. -/
example :
    (swapSplit.hom () ()).hom (0, 1) = (1, 0) ∧
    (swapSplit.reflexive.hom () ()).hom (0, 1) = (0, 0) ∧
    (swapSplit.normalize.hom () ()).hom (0, 1) = (0, 0) := by
  exact ⟨rfl, rfl, rfl⟩

private def diagonal : V ⟶ V :=
  ModuleCat.ofHom ((LinearMap.fst ℤ ℤ ℤ).prod (LinearMap.fst ℤ ℤ ℤ))

private def diagonalSplit : Splitting loop where
  hom _ _ := diagonal
  zero _ _ hn := False.elim (hn (Subsingleton.elim _ _))
  d_h_d _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    rfl

/-- A reflexive inverse can still have a nonzero square; normalization changes it. -/
example :
    (diagonalSplit.reflexive.hom () ()).hom (1, 1) = (1, 1) ∧
    (diagonalSplit.normalize.hom () ()).hom (1, 1) = (0, 0) := by
  exact ⟨rfl, rfl⟩

/-- The normalized inverse has value (-1,-1) on the second basis vector. -/
example : (diagonalSplit.normalize.hom () ()).hom (0, 1) = (-1, -1) := rfl

/-- Squaring separates the reflexive and square-zero normalizations. -/
example :
    (diagonalSplit.reflexive.hom () () ≫
      diagonalSplit.reflexive.hom () ()).hom (1, 0) = (1, 1) ∧
    (diagonalSplit.normalize.hom () () ≫
      diagonalSplit.normalize.hom () ()).hom (1, 0) = (0, 0) := by
  exact ⟨rfl, rfl⟩

/-- The nontrivial loop has the homotopy equivalence furnished by its splitting. -/
example : Nonempty (HomotopyEquiv loop (homologyZeroComplex loop)) :=
  (isSplit_iff_homotopyEquiv_homologyZeroComplex loop).1 ⟨swapSplit⟩

/-- The converse recognizes the concrete normalized homotopy equivalence. -/
example : IsSplit loop :=
  (isSplit_iff_homotopyEquiv_homologyZeroComplex loop).2
    ⟨diagonalSplit.homotopyEquivHomology⟩

/-- The same splitting supplies generalized inverses on every allowed loop edge. -/
example : ∀ i j, (ComplexShape.refl Unit).Rel i j →
    ∃ g : loop.X j ⟶ loop.X i, loop.d i j ≫ g ≫ loop.d i j = loop.d i j :=
  (isSplit_iff_edgewise loop).1 ⟨swapSplit⟩

end NormalizationCounterexamples

section NonsplitProjection

private def double : Z ⟶ Z := ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)

/-- Every term is ℤ; the only nonzero differential is multiplication by two from 1 to 0. -/
private def integerDouble : ChainComplex (ModuleCat ℤ) ℤ := by
  exact
    { X := fun _ => Z
      d := fun i j => if i = 1 ∧ j = 0 then double else 0
      shape := fun i j hn => by
        by_cases h : i = 1 ∧ j = 0
        · rcases h with ⟨rfl, rfl⟩
          exact False.elim (hn (by decide))
        · exact if_neg h
      d_comp_d' := fun i j k _ _ => by
        by_cases h : i = 1 ∧ j = 0
        · rcases h with ⟨rfl, rfl⟩
          simp
        · simp [h] }

private lemma next_zero : (ComplexShape.down ℤ).next 0 = -1 :=
  (ComplexShape.down ℤ).next_eq' (by decide)

private lemma next_one : (ComplexShape.down ℤ).next 1 = 0 :=
  (ComplexShape.down ℤ).next_eq' (by decide)

private lemma prev_zero : (ComplexShape.down ℤ).prev 0 = 1 :=
  (ComplexShape.down ℤ).prev_eq' (by decide)

private lemma double_mono : Mono double := by
  apply (ModuleCat.mono_iff_injective double).2
  intro x y hxy
  change 2 * x = 2 * y at hxy
  omega

private lemma integerDouble_projective_images (i : ℤ) :
    Projective (Abelian.image (integerDouble.d i ((ComplexShape.down ℤ).next i))) := by
  classical
  by_cases hi : i = 1
  · subst i
    rw [next_one]
    change Projective (Abelian.image double)
    let : Mono double := double_mono
    exact Projective.of_iso (asIso (Abelian.factorThruImage double)) inferInstance
  · have hd : integerDouble.d i ((ComplexShape.down ℤ).next i) = 0 := by
      simp [integerDouble, hi]
    rw [hd]
    change Projective (Abelian.image (0 : Z ⟶ Z))
    have hf : Abelian.factorThruImage (0 : Z ⟶ Z) = 0 := by
      apply (cancel_mono (Abelian.image.ι (0 : Z ⟶ Z))).1
      simp only [Abelian.image.fac, zero_comp]
    exact (IsZero.of_epi_eq_zero _ hf).projective

private lemma integerDouble_not_split : ¬ IsSplit integerDouble := by
  rintro ⟨s⟩
  have hv := congrArg (fun f : Z ⟶ Z => f.hom 1) (s.d_h_d (1 : ℤ) 0)
  change 2 * (s.hom 0 1).hom 2 = 2 at hv
  have hl := (s.hom 0 1).hom.map_smul (2 : ℤ) (1 : ℤ)
  change (s.hom 0 1).hom 2 = 2 * (s.hom 0 1).hom 1 at hl
  rw [hl] at hv
  omega

private abbrev residueModule := ModuleCat.of ℤ (ZMod 2)

private def residue : Z ⟶ residueModule :=
  ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap

private lemma double_residue : double ≫ residue = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((2 * x : ℤ) : ZMod 2) = 0
  simp

private def homologyResidue :
    {f : integerDouble.homology 0 ⟶ residueModule //
      integerDouble.homologyπ 0 ≫ f = integerDouble.iCycles 0 ≫ residue} :=
  CokernelCofork.IsColimit.desc'
    (integerDouble.homologyIsCokernel (i := 1) (j := 0) prev_zero)
    (integerDouble.iCycles 0 ≫ residue) (by
      rw [← Category.assoc, integerDouble.toCycles_i]
      change double ≫ residue = 0
      exact double_residue)

private lemma projection_residue :
    (homologyProjection integerDouble integerDouble_projective_images).f 0 ≫
      homologyResidue.1 = residue := by
  let l : Z ⟶ integerDouble.cycles 0 :=
    integerDouble.liftCycles (𝟙 Z) (-1) next_zero (by
      change (𝟙 Z) ≫ (0 : Z ⟶ Z) = 0
      simp only [comp_zero])
  have hl : l ≫ integerDouble.iCycles 0 = 𝟙 Z :=
    integerDouble.liftCycles_i (𝟙 Z) (-1) next_zero _
  have hq := iCycles_homologyProjection_f integerDouble integerDouble_projective_images 0
  calc
    _ = (l ≫ integerDouble.iCycles 0) ≫
        (homologyProjection integerDouble integerDouble_projective_images).f 0 ≫
          homologyResidue.1 := by rw [hl, Category.id_comp]
    _ = l ≫ (integerDouble.iCycles 0 ≫
        (homologyProjection integerDouble integerDouble_projective_images).f 0) ≫
          homologyResidue.1 := by simp only [Category.assoc]
    _ = l ≫ integerDouble.homologyπ 0 ≫ homologyResidue.1 := by rw [hq]
    _ = l ≫ (integerDouble.iCycles 0 ≫ residue) := by
      simp only [Category.assoc, homologyResidue.2]
    _ = residue := by rw [← Category.assoc, hl, Category.id_comp]

/-- The arbitrary projective-image projection carries 1 to the nonzero residue class. -/
example :
    ((homologyProjection integerDouble integerDouble_projective_images).f 0 ≫
      homologyResidue.1).hom 1 = (1 : ZMod 2) := by
  rw [projection_residue]
  rfl

/-- This projection has a genuinely nonzero degree-zero component. -/
example : (homologyProjection integerDouble integerDouble_projective_images).f 0 ≠ 0 := by
  intro hz
  have h := projection_residue
  rw [hz, zero_comp] at h
  have hv := congrArg (fun f : Z ⟶ residueModule => f.hom 1) h
  change (0 : ZMod 2) = 1 at hv
  exact zero_ne_one hv

/-- Projective outgoing images give a quasi-isomorphism even though this complex is not split. -/
example : QuasiIso (homologyProjection integerDouble integerDouble_projective_images) :=
  quasiIso_homologyProjection integerDouble integerDouble_projective_images

/-- No homotopy equivalence to the zero-differential homology complex exists here. -/
example : ¬ Nonempty (HomotopyEquiv integerDouble (homologyZeroComplex integerDouble)) := by
  intro h
  exact integerDouble_not_split
    ((isSplit_iff_homotopyEquiv_homologyZeroComplex integerDouble).2 h)

/-- The integer degree-one criterion detects the same obstruction 4s(1)=2. -/
example : ¬ (∃ s : ∀ n : ℤ, integerDouble.X n ⟶ integerDouble.X (n + 1),
    ∀ n : ℤ, integerDouble.d (n + 1) n =
      integerDouble.d (n + 1) n ≫ s n ≫ integerDouble.d (n + 1) n) := by
  intro h
  exact integerDouble_not_split
    ((ChainComplex.isSplit_iff_exists_degreeOneHom integerDouble).2 h)

end NonsplitProjection

section ConcreteShiftCoherence

/-- The zero-shift comparison and its inverse both retain the nonzero integer 7. -/
example :
    (((ChainComplex.nativeShiftZero (ModuleCat ℤ)).hom.app integerDouble).f 0).hom 7 = 7 ∧
    (((ChainComplex.nativeShiftZero (ModuleCat ℤ)).inv.app integerDouble).f 0).hom 7 = 7 := by
  constructor
  · rw [ChainComplex.nativeShiftZero_hom_app_f]
    rfl
  · rw [ChainComplex.nativeShiftZero_inv_app_f]
    rfl

/-- Shifting the actual ×2 edge down by one produces the negative value in degree 0→-1. -/
example :
    (((ChainComplex.nativeShift (ModuleCat ℤ) (-1)).obj integerDouble).d 0 (-1)).hom 7 =
      -14 := by
  simp [ChainComplex.nativeShift_obj_d, integerDouble, double]

/-- The addition comparison carries 7 unchanged between the two genuine shifts by one. -/
example :
    (((ChainComplex.nativeShiftAdd (ModuleCat ℤ) 1 1).hom.app integerDouble).f 3).hom 7 = 7 ∧
    (((ChainComplex.nativeShiftAdd (ModuleCat ℤ) 1 1).inv.app integerDouble).f 3).hom 7 = 7 := by
  constructor
  · rw [ChainComplex.nativeShiftAdd_hom_app_f]
    rfl
  · rw [ChainComplex.nativeShiftAdd_inv_app_f]
    rfl

/-- Two odd shifts restore the positive ×2 differential, at its new indices 3→2. -/
example :
    (((ChainComplex.nativeShift (ModuleCat ℤ) 2).obj integerDouble).d 3 2).hom 7 = 14 ∧
    (((ChainComplex.nativeShift (ModuleCat ℤ) 1).obj
      ((ChainComplex.nativeShift (ModuleCat ℤ) 1).obj integerDouble)).d 3 2).hom 7 = 14 := by
  constructor <;> simp [ChainComplex.nativeShift_obj_d, integerDouble, double]

end ConcreteShiftCoherence

section TensorComparison

private abbrev singleZ := (ChainComplex.single₀ (ModuleCat ℤ)).obj Z

private def singleSplit : Functor.AugmentationSplit (𝟭 (ModuleCat ℤ)) singleZ Z (𝟙 singleZ) where
  section_ := 𝟙 Z
  s _ := 0
  section_comp := by simp
  zero := by simp
  succ n :=
    (isZero_single_obj_X (ComplexShape.down ℕ) 0 Z (n + 1) (by omega)).eq_of_src _ _

private def singleRelativeProjective (n : ℕ) :
    (𝟭 (ModuleCat ℤ)).IsRelativeProjective (singleZ.X n) :=
  (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).isRelativeProjective_obj _

/-- The tensor homology comparison over ×2 is computed by the explicit single-complex chain map. -/
example :
    ModuleCat.tensorRelativeComparisonHomologyMap (𝟭 (ModuleCat ℤ)) Z
      singleZ singleZ Z Z (𝟙 singleZ) (𝟙 singleZ) singleSplit singleRelativeProjective
        (fun _ => inferInstance) double 0 =
      homologyMap
        (((ModuleCat.relativeTensorFunctor (R := ℤ) Z).mapHomologicalComplex
          (ComplexShape.down ℕ)).map ((ChainComplex.single₀ (ModuleCat ℤ)).map double)) 0 :=
  ModuleCat.tensorRelativeComparisonHomologyMap_eq_of_augmentation (𝟭 (ModuleCat ℤ)) Z
    singleZ singleZ Z Z (𝟙 singleZ) (𝟙 singleZ) singleSplit singleRelativeProjective
      (fun _ => inferInstance) double ((ChainComplex.single₀ (ModuleCat ℤ)).map double)
        (by simp) 0

/-- The isomorphism's forward comparison over the identity is the identity on tensor homology. -/
example (n : ℕ) :
    (ModuleCat.tensorRelativeResolutionHomologyIso (𝟭 (ModuleCat ℤ)) V
      singleZ singleZ Z (𝟙 singleZ) (𝟙 singleZ) singleSplit singleSplit
        singleRelativeProjective singleRelativeProjective
          (fun _ => inferInstance) (fun _ => inferInstance) n).hom = 𝟙 _ := by
  rw [ModuleCat.tensorRelativeResolutionHomologyIso_hom]
  exact Functor.comparisonHomologyMap_id (𝟭 (ModuleCat ℤ))
    (ModuleCat.relativeTensorFunctor V) singleZ Z (𝟙 singleZ) singleSplit
      singleRelativeProjective (fun _ => inferInstance) n

/-- Tensoring the nonidentity ×2 comparison takes 2⊗3 to a tensor detected by 12. -/
example :
    (TensorProduct.lid ℤ ℤ).toLinearMap
      (((((ModuleCat.relativeTensorFunctor (R := ℤ) Z).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          ((ChainComplex.single₀ (ModuleCat ℤ)).map double)).f 0).hom (2 ⊗ₜ[ℤ] 3)) = 12 := by
  change (TensorProduct.lid ℤ ℤ).toLinearMap
    (((ModuleCat.relativeTensorFunctor (R := ℤ) Z).map
      (((ChainComplex.single₀ (ModuleCat ℤ)).map double).f 0)).hom (2 ⊗ₜ[ℤ] 3)) = 12
  rw [ChainComplex.single₀_map_f_zero]
  change (TensorProduct.lid ℤ ℤ).toLinearMap
    (TensorProduct.map LinearMap.id double.hom (2 ⊗ₜ[ℤ] 3)) = 12
  simp [TensorProduct.map_tmul, double]

end TensorComparison

end MathlibExtTest.Algebra.Homology.DerivedTransport
