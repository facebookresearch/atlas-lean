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
        · exact ite_eq_right h
      d_comp_d' := fun i j k _ _ => by
        by_cases h : i = 1 ∧ j = 0
        · rcases h with ⟨rfl, rfl⟩
          simp
        · simp [h] }

private def integerXIso (i : ℤ) : integerDouble.X i ≅ Z := eqToIso rfl

private lemma next_zero : (ComplexShape.down ℤ).next 0 = -1 :=
  (ComplexShape.down ℤ).next_eq' (by decide)

private lemma next_one : (ComplexShape.down ℤ).next 1 = 0 :=
  (ComplexShape.down ℤ).next_eq' (by decide)

private lemma prev_zero : (ComplexShape.down ℤ).prev 0 = 1 :=
  (ComplexShape.down ℤ).prev_eq' (by decide)

private lemma double_mono : Mono double := by
  apply (ModuleCat.mono_iff_injective double).2
  change Function.Injective (fun x : ℤ => (2 : ℤ) * x)
  intro x y hxy
  change (2 : ℤ) * x = (2 : ℤ) * y at hxy
  omega

private lemma integerDouble_projective_images (i : ℤ) :
    Projective (Abelian.image (integerDouble.d i ((ComplexShape.down ℤ).next i))) := by
  by_cases hi : i = 1
  · subst i
    rw [next_one]
    change Projective (Abelian.image double)
    let : Mono double := double_mono
    exact Projective.of_iso (asIso (Abelian.factorThruImage double)) inferInstance
  · have hd : integerDouble.d i ((ComplexShape.down ℤ).next i) = 0 := by
      change (if i = 1 ∧ (ComplexShape.down ℤ).next i = 0 then double else (0 : Z ⟶ Z)) = 0
      exact ite_eq_right (fun h => hi h.1)
    rw [hd]
    change Projective (Abelian.image (0 : Z ⟶ Z))
    have hf : Abelian.factorThruImage (0 : Z ⟶ Z) = 0 := by
      apply (cancel_mono (Abelian.image.ι (0 : Z ⟶ Z))).1
      simp only [Abelian.image.fac, zero_comp]
    exact (IsZero.of_epi_eq_zero _ hf).projective

private lemma integerDouble_not_split : ¬ IsSplit integerDouble := by
  rintro ⟨s⟩
  let t : Z ⟶ Z := s.hom 0 1
  have hs : double ≫ t ≫ double = double := s.d_h_d (1 : ℤ) 0
  let k : ℤ := t.hom (1 : ℤ)
  have hl : (show ℤ from t.hom (2 : ℤ)) = (2 : ℤ) * k := by
    have h := t.hom.map_smul (2 : ℤ) (1 : ℤ)
    change (show ℤ from t.hom (2 : ℤ)) = (2 : ℤ) * (show ℤ from t.hom (1 : ℤ)) at h
    exact h
  have hv : (2 : ℤ) * (show ℤ from t.hom (2 : ℤ)) = 2 := by
    have h := congrArg (fun f : Z ⟶ Z => (show ℤ from f.hom (1 : ℤ))) hs
    change (2 : ℤ) * (show ℤ from t.hom (2 : ℤ)) = 2 at h
    exact h
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
  rw [Int.cast_mul]
  have h2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

private def cyclesInclusion : integerDouble.cycles 0 ⟶ Z :=
  integerDouble.iCycles 0 ≫ (integerXIso 0).hom

private def homologyXIso : (homologyZeroComplex integerDouble).X 0 ≅ integerDouble.homology 0 :=
  eqToIso rfl

private def projectionZero : Z ⟶ integerDouble.homology 0 :=
  (integerXIso 0).inv ≫ (homologyProjection integerDouble integerDouble_projective_images).f 0 ≫
    homologyXIso.hom

private lemma cycles_residue_zero : integerDouble.toCycles 1 0 ≫ cyclesInclusion ≫ residue = 0 := by
  apply zero_of_epi_comp (integerXIso 1).inv
  calc
    _ = ((integerXIso 1).inv ≫ integerDouble.d 1 0 ≫ (integerXIso 0).hom) ≫ residue := by
      have h := congrArg
        (fun f : integerDouble.X 1 ⟶ integerDouble.X 0 =>
          (integerXIso 1).inv ≫ f ≫ (integerXIso 0).hom ≫ residue)
        (integerDouble.toCycles_i 1 0)
      simpa only [cyclesInclusion, Category.assoc] using h
    _ = double ≫ residue := by
      have hd : (integerXIso 1).inv ≫ integerDouble.d 1 0 ≫ (integerXIso 0).hom = double := by
        change (𝟙 Z) ≫ double ≫ (𝟙 Z) = double
        simp only [Category.id_comp, Category.comp_id]
      rw [hd]
    _ = 0 := double_residue

private def homologyResidue :
    {f : integerDouble.homology 0 ⟶ residueModule //
      integerDouble.homologyπ 0 ≫ f = cyclesInclusion ≫ residue} :=
  CokernelCofork.IsColimit.desc'
    (integerDouble.homologyIsCokernel (i := 1) (j := 0) prev_zero)
    (cyclesInclusion ≫ residue) cycles_residue_zero

private def integerCycleLift : Z ⟶ integerDouble.cycles 0 :=
  integerDouble.liftCycles (integerXIso 0).inv (-1) next_zero (by
    have hd : integerDouble.d 0 (-1) = 0 := by
      change (0 : Z ⟶ Z) = 0
      rfl
    rw [hd, comp_zero])

private lemma cycleLift_inclusion : integerCycleLift ≫ cyclesInclusion = 𝟙 Z := by
  have h : integerCycleLift ≫ integerDouble.iCycles 0 = (integerXIso 0).inv :=
    integerDouble.liftCycles_i (integerXIso 0).inv (-1) next_zero _
  calc
    _ = (integerCycleLift ≫ integerDouble.iCycles 0) ≫ (integerXIso 0).hom := by
      simp only [cyclesInclusion, Category.assoc]
    _ = (integerXIso 0).inv ≫ (integerXIso 0).hom :=
      congrArg (fun f : Z ⟶ integerDouble.X 0 => f ≫ (integerXIso 0).hom) h
    _ = 𝟙 Z := (integerXIso 0).inv_hom_id

private lemma inclusion_projection :
    cyclesInclusion ≫ projectionZero = integerDouble.homologyπ 0 := by
  have h : integerDouble.iCycles 0 ≫
      (homologyProjection integerDouble integerDouble_projective_images).f 0 =
        integerDouble.homologyπ 0 ≫ homologyXIso.inv :=
    iCycles_homologyProjection_f integerDouble integerDouble_projective_images 0
  calc
    _ = (integerDouble.iCycles 0 ≫
        (homologyProjection integerDouble integerDouble_projective_images).f 0) ≫
          homologyXIso.hom := by
      simp only [cyclesInclusion, projectionZero, Category.assoc, Iso.hom_inv_id_assoc]
    _ = (integerDouble.homologyπ 0 ≫ homologyXIso.inv) ≫ homologyXIso.hom :=
      congrArg
        (fun f : integerDouble.cycles 0 ⟶ (homologyZeroComplex integerDouble).X 0 =>
          f ≫ homologyXIso.hom) h
    _ = integerDouble.homologyπ 0 := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma projection_factor {B C D : ModuleCat ℤ}
    (l : Z ⟶ B) (i : B ⟶ Z) (p : Z ⟶ C) (π : B ⟶ C) (r : C ⟶ D) (v : Z ⟶ D)
    (hli : l ≫ i = 𝟙 Z) (hip : i ≫ p = π) (hπr : π ≫ r = i ≫ v) :
    p ≫ r = v := by
  calc
    _ = (l ≫ i) ≫ p ≫ r := by rw [hli, Category.id_comp]
    _ = (l ≫ (i ≫ p)) ≫ r := by simp only [Category.assoc]
    _ = (l ≫ π) ≫ r := congrArg (fun f : B ⟶ C => (l ≫ f) ≫ r) hip
    _ = l ≫ (π ≫ r) := Category.assoc l π r
    _ = l ≫ (i ≫ v) := congrArg (fun f : B ⟶ D => l ≫ f) hπr
    _ = (l ≫ i) ≫ v := (Category.assoc l i v).symm
    _ = v := by rw [hli, Category.id_comp]

private lemma projection_residue : projectionZero ≫ homologyResidue.1 = residue :=
  projection_factor integerCycleLift cyclesInclusion projectionZero
    (integerDouble.homologyπ 0) homologyResidue.1 residue
      cycleLift_inclusion inclusion_projection homologyResidue.2

/-- In its native ℤ coordinate, the projection carries 1 to the nonzero residue class. -/
example : (projectionZero ≫ homologyResidue.1).hom (1 : ℤ) = (1 : ZMod 2) := by
  rw [projection_residue]
  rfl

/-- This projection has a genuinely nonzero degree-zero component. -/
example : (homologyProjection integerDouble integerDouble_projective_images).f 0 ≠ 0 := by
  intro hz
  have hq : projectionZero = 0 := by
    simp only [projectionZero, hz, zero_comp, comp_zero]
  have h := projection_residue
  rw [hq, zero_comp] at h
  have hv := congrArg (fun f : Z ⟶ residueModule => (show ZMod 2 from f.hom (1 : ℤ))) h
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

private def shiftXIso (a i : ℤ) :
    ((ChainComplex.nativeShift (ModuleCat ℤ) a).obj integerDouble).X i ≅ Z :=
  ChainComplex.nativeShiftObjXIso integerDouble a i ≪≫ integerXIso (i - a)

private def twiceXIso (i : ℤ) :
    ((ChainComplex.nativeShift (ModuleCat ℤ) 1).obj
      ((ChainComplex.nativeShift (ModuleCat ℤ) 1).obj integerDouble)).X i ≅ Z :=
  ChainComplex.nativeShiftObjXIso
      ((ChainComplex.nativeShift (ModuleCat ℤ) 1).obj integerDouble) 1 i ≪≫ shiftXIso 1 (i - 1)

private def coordinateShiftD (K : ChainComplex (ModuleCat ℤ) ℤ)
    (e : ∀ i : ℤ, K.X i ≅ Z) (a i j i' j' : ℤ) (hi : i - a = i') (hj : j - a = j') :
    Z ⟶ Z :=
  (e i').inv ≫
    ((ChainComplex.nativeShiftObjXIso' K a i i' hi).inv ≫
      ((ChainComplex.nativeShift (ModuleCat ℤ) a).obj K).d i j ≫
        (ChainComplex.nativeShiftObjXIso' K a j j' hj).hom) ≫ (e j').hom

private lemma coordinateShiftD_eq (K : ChainComplex (ModuleCat ℤ) ℤ)
    (e : ∀ i : ℤ, K.X i ≅ Z) (a i j i' j' : ℤ) (hi : i - a = i') (hj : j - a = j') :
    coordinateShiftD K e a i j i' j' hi hj =
      (e i').inv ≫ (a.negOnePow • K.d i' j') ≫ (e j').hom := by
  unfold coordinateShiftD
  rw [ChainComplex.nativeShiftObjXIso'_inv_d_hom]

/-- The zero-shift comparison and its inverse retain 7 in the earned component coordinates. -/
example :
    ((shiftXIso 0 0).inv ≫
      ((ChainComplex.nativeShiftZero (ModuleCat ℤ)).hom.app integerDouble).f 0 ≫
        (integerXIso 0).hom).hom (7 : ℤ) = (7 : ℤ) ∧
    ((integerXIso 0).inv ≫
      ((ChainComplex.nativeShiftZero (ModuleCat ℤ)).inv.app integerDouble).f 0 ≫
        (shiftXIso 0 0).hom).hom (7 : ℤ) = (7 : ℤ) := by
  constructor
  · rw [ChainComplex.nativeShiftZero_hom_app_f]
    rfl
  · rw [ChainComplex.nativeShiftZero_inv_app_f]
    rfl

/-- The actual ×2 edge shifted down by one has value -14 in degrees 0→-1. -/
example :
    (coordinateShiftD integerDouble integerXIso (-1) 0 (-1) 1 0
      (by decide) (by decide)).hom (7 : ℤ) = (-14 : ℤ) := by
  rw [coordinateShiftD_eq]
  change ((-1 : ℤ).negOnePow • double).hom (7 : ℤ) = (-14 : ℤ)
  have hs : (-1 : ℤ).negOnePow = (-1 : ℤˣ) := by decide
  rw [hs]
  change -((2 : ℤ) * 7) = (-14 : ℤ)
  rfl

/-- The addition comparison carries 7 between a shift by two and the two shifts by one. -/
example :
    ((shiftXIso 2 3).inv ≫
      ((ChainComplex.nativeShiftAdd (ModuleCat ℤ) 1 1).hom.app integerDouble).f 3 ≫
        (twiceXIso 3).hom).hom (7 : ℤ) = (7 : ℤ) ∧
    ((twiceXIso 3).inv ≫
      ((ChainComplex.nativeShiftAdd (ModuleCat ℤ) 1 1).inv.app integerDouble).f 3 ≫
        (shiftXIso 2 3).hom).hom (7 : ℤ) = (7 : ℤ) := by
  constructor
  · rw [ChainComplex.nativeShiftAdd_hom_app_f]
    rfl
  · rw [ChainComplex.nativeShiftAdd_inv_app_f]
    rfl

/-- Two odd shifts restore the positive ×2 edge, in its earned degree-3→2 coordinates. -/
example :
    (coordinateShiftD integerDouble integerXIso 2 3 2 1 0
      (by decide) (by decide)).hom (7 : ℤ) = (14 : ℤ) ∧
    (coordinateShiftD ((ChainComplex.nativeShift (ModuleCat ℤ) 1).obj integerDouble)
      (shiftXIso 1) 1 3 2 2 1 (by decide) (by decide)).hom (7 : ℤ) = (14 : ℤ) := by
  constructor
  · rw [coordinateShiftD_eq]
    change ((2 : ℤ).negOnePow • double).hom (7 : ℤ) = (14 : ℤ)
    have hs : (2 : ℤ).negOnePow = (1 : ℤˣ) := by decide
    rw [hs, one_smul]
    change (2 : ℤ) * 7 = 14
    rfl
  · rw [coordinateShiftD_eq]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul]
    change ((1 : ℤ).negOnePow •
      coordinateShiftD integerDouble integerXIso 1 2 1 1 0
        (by decide) (by decide)).hom (7 : ℤ) = (14 : ℤ)
    rw [coordinateShiftD_eq]
    change ((1 : ℤ).negOnePow • ((1 : ℤ).negOnePow • double)).hom (7 : ℤ) = (14 : ℤ)
    have hs : (1 : ℤ).negOnePow = (-1 : ℤˣ) := by decide
    rw [hs]
    change (2 : ℤ) * 7 = 14
    rfl

end ConcreteShiftCoherence

section TensorComparison

private abbrev singleZ := (ChainComplex.single₀ (ModuleCat ℤ)).obj Z

private abbrev tensorZ : ModuleCat ℤ ⥤ ModuleCat ℤ :=
  ModuleCat.relativeTensorFunctor (R := ℤ) Z

private def tensorSingleCoordinate : tensorZ.obj (singleZ.X 0) ≅ tensorZ.obj Z :=
  tensorZ.mapIso (singleObjXSelf (ComplexShape.down ℕ) 0 Z)

private def tensorDoubleZero : tensorZ.obj Z ⟶ tensorZ.obj Z :=
  tensorSingleCoordinate.inv ≫
    (((tensorZ.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((ChainComplex.single₀ (ModuleCat ℤ)).map double)).f 0) ≫ tensorSingleCoordinate.hom

private lemma tensorDoubleZero_eq : tensorDoubleZero = tensorZ.map double := by
  unfold tensorDoubleZero
  change tensorSingleCoordinate.inv ≫
    tensorZ.map (((ChainComplex.single₀ (ModuleCat ℤ)).map double).f 0) ≫
      tensorSingleCoordinate.hom = tensorZ.map double
  rw [ChainComplex.single₀_map_f_zero]
  change tensorZ.map (𝟙 Z) ≫ tensorZ.map double ≫ tensorZ.map (𝟙 Z) = tensorZ.map double
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]

private def singleSplit : Functor.AugmentationSplit (𝟭 (ModuleCat ℤ)) singleZ Z (𝟙 singleZ) where
  section_ := 𝟙 Z
  s _ := 0
  section_comp := by simp
  zero := by
    change (𝟙 Z) + (0 : Z ⟶ singleZ.X 1) ≫ (0 : singleZ.X 1 ⟶ Z) = 𝟙 Z
    simp only [zero_comp, add_zero]
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
      (tensorDoubleZero.hom ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ))) = (12 : ℤ) := by
  rw [tensorDoubleZero_eq]
  change (TensorProduct.lid ℤ ℤ).toLinearMap
    (TensorProduct.map LinearMap.id double.hom ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ))) = (12 : ℤ)
  simp [TensorProduct.map_tmul, double]

end TensorComparison

end MathlibExtTest.Algebra.Homology.DerivedTransport
