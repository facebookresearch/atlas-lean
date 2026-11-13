/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FrontierA.FunctionalBKRGeneralDual
import Code.FrontierA.FunctionalBKRGeneralFinite

open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


def piAgreeOn (K : Set E) (x y : ∀ e, S e) : Prop :=
  ∀ e, e ∈ K → x e = y e

@[refl] theorem piAgreeOn_refl (K : Set E) (x : ∀ e, S e) :
    piAgreeOn K x x := fun _ _ => rfl


noncomputable def piAgreementFiber (K : Set E) (x : ∀ e, S e) :
    Finset (∀ e, S e) := by
  classical
  exact Finset.univ.filter (piAgreeOn K x)

@[simp] theorem mem_piAgreementFiber {K : Set E} {x y : ∀ e, S e} :
    y ∈ piAgreementFiber K x ↔ piAgreeOn K x y := by
  classical
  simp [piAgreementFiber]

theorem piAgreementFiber_nonempty (K : Set E) (x : ∀ e, S e) :
    (piAgreementFiber K x).Nonempty := by
  classical
  exact ⟨x, mem_piAgreementFiber.mpr (piAgreeOn_refl K x)⟩


noncomputable def piCylinderMin (f : (∀ e, S e) → ℝ) (K : Set E)
    (x : ∀ e, S e) : ℝ :=
  (piAgreementFiber K x).inf' (piAgreementFiber_nonempty K x) f



noncomputable def piFunctionalDisjointMaxAt
    (f g : (∀ e, S e) → ℝ) (x y : ∀ e, S e) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => piCylinderMin f pair.1 x * piCylinderMin g pair.2 y


noncomputable def piFunctionalDisjointMax
    (f g : (∀ e, S e) → ℝ) (x : ∀ e, S e) : ℝ :=
  piFunctionalDisjointMaxAt f g x x


def decodeBlockConfig (decode : ∀ e, (D → Bool) → S e)
    (omega : ConfigSpace (E × D)) : ∀ e, S e :=
  fun e => decode e (fun d => omega (e, d))


def wholeBlocks (K : Set E) : Set (E × D) :=
  {z | z.1 ∈ K}

theorem wholeBlocks_disjoint {K L : Set E} (hKL : Disjoint K L) :
    Disjoint (wholeBlocks (D := D) K) (wholeBlocks (D := D) L) := by
  rw [Set.disjoint_left]
  intro z hzK hzL
  exact Set.disjoint_left.1 hKL hzK hzL


noncomputable def encodeBlockConfig
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e)) (x : ∀ e, S e) :
    ConfigSpace (E × D) :=
  fun z => Classical.choose (hdecode z.1 (x z.1)) z.2

@[simp] theorem decodeBlockConfig_encodeBlockConfig
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e)) (x : ∀ e, S e) :
    decodeBlockConfig decode (encodeBlockConfig decode hdecode x) = x := by
  funext e
  exact Classical.choose_spec (hdecode e (x e))



noncomputable def liftPiCylinder
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : ConfigSpace (E × D)) (x : ∀ e, S e) :
    ConfigSpace (E × D) := by
  classical
  exact fun z => if z.1 ∈ K then omega z else encodeBlockConfig decode hdecode x z

theorem liftPiCylinder_agreeOn
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : ConfigSpace (E × D)) (x : ∀ e, S e) :
    agreeOn (wholeBlocks (D := D) K) omega
      (liftPiCylinder decode hdecode K omega x) := by
  intro z hz
  simp only [wholeBlocks, Set.mem_setOf_eq] at hz
  simp [liftPiCylinder, hz]

theorem decodeBlockConfig_liftPiCylinder
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : ConfigSpace (E × D)) (x : ∀ e, S e)
    (hx : piAgreeOn K (decodeBlockConfig decode omega) x) :
    decodeBlockConfig decode (liftPiCylinder decode hdecode K omega x) = x := by
  funext e
  by_cases he : e ∈ K
  · simpa [decodeBlockConfig, liftPiCylinder, he] using hx e he
  · simpa [decodeBlockConfig, liftPiCylinder, he] using
      congrFun (decodeBlockConfig_encodeBlockConfig decode hdecode x) e

theorem piAgreeOn_decode_of_agreeOn_wholeBlocks
    (decode : ∀ e, (D → Bool) → S e) (K : Set E)
    {omega eta : ConfigSpace (E × D)}
    (h : agreeOn (wholeBlocks (D := D) K) omega eta) :
    piAgreeOn K (decodeBlockConfig decode omega) (decodeBlockConfig decode eta) := by
  intro e he
  apply congrArg (decode e)
  funext d
  exact (h (e, d) he).symm



theorem piCylinderMin_decodeBlockConfig
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f : (∀ e, S e) → ℝ) (K : Set E) (omega : ConfigSpace (E × D)) :
    piCylinderMin f K (decodeBlockConfig decode omega) =
      cylinderMin (f ∘ decodeBlockConfig decode) (wholeBlocks (D := D) K) omega := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro eta heta
    exact Finset.inf'_le _ (mem_piAgreementFiber.mpr
      (piAgreeOn_decode_of_agreeOn_wholeBlocks decode K
        (mem_agreementFiber.mp heta)))
  · apply Finset.le_inf'
    intro x hx
    let eta := liftPiCylinder decode hdecode K omega x
    have heta : eta ∈ agreementFiber (wholeBlocks (D := D) K) omega :=
      mem_agreementFiber.mpr (liftPiCylinder_agreeOn decode hdecode K omega x)
    calc
      cylinderMin (f ∘ decodeBlockConfig decode) (wholeBlocks (D := D) K) omega
          ≤ (f ∘ decodeBlockConfig decode) eta := Finset.inf'_le _ heta
      _ = f x := by
        rw [Function.comp_apply, decodeBlockConfig_liftPiCylinder decode hdecode
          K omega x (mem_piAgreementFiber.mp hx)]



theorem piFunctionalDisjointMaxAt_decode_le
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ) (omega eta : ConfigSpace (E × D)) :
    piFunctionalDisjointMaxAt f g (decodeBlockConfig decode omega)
        (decodeBlockConfig decode eta) ≤
      functionalDisjointMaxAt (f ∘ decodeBlockConfig decode)
        (g ∘ decodeBlockConfig decode) omega eta := by
  classical
  unfold piFunctionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  rw [piCylinderMin_decodeBlockConfig decode hdecode,
    piCylinderMin_decodeBlockConfig decode hdecode]
  unfold functionalDisjointMaxAt
  have hbit : (wholeBlocks (D := D) pair.1, wholeBlocks (D := D) pair.2) ∈
      disjointCoordinatePairs (E × D) :=
    mem_disjointCoordinatePairs.mpr
      (wholeBlocks_disjoint (D := D) (mem_disjointCoordinatePairs.mp hpair))
  exact Finset.le_sup'
    (fun bitPair : Set (E × D) × Set (E × D) =>
      cylinderMin (f ∘ decodeBlockConfig decode) bitPair.1 omega *
        cylinderMin (g ∘ decodeBlockConfig decode) bitPair.2 eta)
    hbit

theorem piFunctionalDisjointMax_decode_le
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ) (omega : ConfigSpace (E × D)) :
    piFunctionalDisjointMax f g (decodeBlockConfig decode omega) ≤
      functionalDisjointMax (f ∘ decodeBlockConfig decode)
        (g ∘ decodeBlockConfig decode) omega :=
  piFunctionalDisjointMaxAt_decode_le decode hdecode f g omega omega



noncomputable def blockProductExpectation
    (phi : E × D → Bool → ℝ) (decode : ∀ e, (D → Bool) → S e)
    (f : (∀ e, S e) → ℝ) : ℝ :=
  productExpectation phi (f ∘ decodeBlockConfig decode)



theorem functionalBKR_finiteCoordinateBlocks
    (phi : E × D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    blockProductExpectation phi decode (piFunctionalDisjointMax f g) ≤
      blockProductExpectation phi decode f * blockProductExpectation phi decode g := by
  unfold blockProductExpectation
  calc
    productExpectation phi (piFunctionalDisjointMax f g ∘ decodeBlockConfig decode) ≤
        productExpectation phi
          (functionalDisjointMax (f ∘ decodeBlockConfig decode)
            (g ∘ decodeBlockConfig decode)) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalDisjointMax_decode_le decode hdecode f g omega)
        (pweight_nonneg hphi0 omega)
    _ ≤ productExpectation phi (f ∘ decodeBlockConfig decode) *
          productExpectation phi (g ∘ decodeBlockConfig decode) :=
      functionalBKR_real phi hphi0 hphi1 _ _
        (fun omega => hf0 (decodeBlockConfig decode omega))
        (fun omega => hg0 (decodeBlockConfig decode omega))


theorem dualFunctionalBKR_finiteCoordinateBlocks
    (phi : E × D → Bool → ℝ)
    (hphi0 : ∀ z b, 0 ≤ phi z b)
    (hphi1 : ∀ z, phi z false + phi z true = 1)
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (f g : (∀ e, S e) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    dualProductExpectation phi (fun pair =>
        piFunctionalDisjointMaxAt f g (decodeBlockConfig decode pair.1)
          (decodeBlockConfig decode pair.2)) ≤
      blockProductExpectation phi decode (fun x => f x * g x) := by
  unfold blockProductExpectation
  calc
    dualProductExpectation phi (fun pair =>
        piFunctionalDisjointMaxAt f g (decodeBlockConfig decode pair.1)
          (decodeBlockConfig decode pair.2)) ≤
        dualProductExpectation phi (fun pair =>
          functionalDisjointMaxAt (f ∘ decodeBlockConfig decode)
            (g ∘ decodeBlockConfig decode) pair.1 pair.2) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalDisjointMaxAt_decode_le decode hdecode f g omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ ≤ productExpectation phi
          ((fun x => f x * g x) ∘ decodeBlockConfig decode) := by
      exact dualFunctionalBKR_real phi hphi0 hphi1 _ _
        (fun omega => hf0 (decodeBlockConfig decode omega))
        (fun omega => hg0 (decodeBlockConfig decode omega))

end StatMech.FrontierA
