/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPartialPauliData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPauliState

/-! The nine original spin stages satisfy their certified anchored Pauli phase formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual prefixes of the original eight-factor spin word. -/
def generatedSixthPartialWordOf (p q x : SpinHolomorph) : Fin 9 → SpinHolomorph :=
  ![1,
    p,
    x * p,
    p * (x * p),
    q * (p * (x * p)),
    p * (q * (p * (x * p))),
    x * (p * (q * (p * (x * p)))),
    q * (x * (p * (q * (p * (x * p))))),
    x * (q * (x * (p * (q * (p * (x * p))))))]

/-- The original spin normalizers inserted into the prefix construction. -/
def generatedSixthPartialSpinWord : Fin 9 → SpinHolomorph :=
  generatedSixthPartialWordOf (monsterSourcePermutationSpin 0)
    (monsterSourcePermutationSpin 1) xiSpinHolomorph

/-- The genuine spin state after each prefix of the original word. -/
def generatedSixthPartialSpinState (k : Fin 9) : SpinSpace :=
  (generatedSixthPartialSpinWord k).val (generatedOddSpinState 0 1 0)

private theorem prefix_transport (p q x : SpinHolomorph) (c : Fin 9 → Q)
    (h1 : spinConjugation p (c 0) = c 1)
    (h2 : spinConjugation x (c 1) = c 2)
    (h3 : spinConjugation p (c 2) = c 3)
    (h4 : spinConjugation q (c 3) = c 4)
    (h5 : spinConjugation p (c 4) = c 5)
    (h6 : spinConjugation x (c 5) = c 6)
    (h7 : spinConjugation q (c 6) = c 7)
    (h8 : spinConjugation x (c 7) = c 8) (k : Fin 9) :
    spinConjugation (generatedSixthPartialWordOf p q x k) (c 0) = c k := by
  have hm (u v : SpinHolomorph) (z : Q) :
      spinConjugation (u * v) z = spinConjugation u (spinConjugation v z) :=
    congrArg (fun e : MulAut Q => e z) (map_mul spinConjugation u v)
  have e2 : spinConjugation (x * p) (c 0) = c 2 :=
    (hm x (p) (c 0)).trans
      ((congrArg (spinConjugation x) h1).trans h2)
  have e3 : spinConjugation (p * (x * p)) (c 0) = c 3 :=
    (hm p (x * p) (c 0)).trans
      ((congrArg (spinConjugation p) e2).trans h3)
  have e4 : spinConjugation (q * (p * (x * p))) (c 0) = c 4 :=
    (hm q (p * (x * p)) (c 0)).trans
      ((congrArg (spinConjugation q) e3).trans h4)
  have e5 : spinConjugation (p * (q * (p * (x * p)))) (c 0) = c 5 :=
    (hm p (q * (p * (x * p))) (c 0)).trans
      ((congrArg (spinConjugation p) e4).trans h5)
  have e6 : spinConjugation (x * (p * (q * (p * (x * p))))) (c 0) = c 6 :=
    (hm x (p * (q * (p * (x * p)))) (c 0)).trans
      ((congrArg (spinConjugation x) e5).trans h6)
  have e7 : spinConjugation (q * (x * (p * (q * (p * (x * p)))))) (c 0) = c 7 :=
    (hm q (x * (p * (q * (p * (x * p))))) (c 0)).trans
      ((congrArg (spinConjugation q) e6).trans h7)
  have e8 : spinConjugation (x * (q * (x * (p * (q * (p * (x * p))))))) (c 0) = c 8 :=
    (hm x (q * (x * (p * (q * (p * (x * p)))))) (c 0)).trans
      ((congrArg (spinConjugation x) e7).trans h8)
  fin_cases k
  · change spinConjugation 1 (c 0) = c 0
    exact congrArg (fun e : MulAut Q => e (c 0)) (map_one spinConjugation)
  · exact h1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7
  · exact e8

/-- Each original prefix transports its twelve initial Pauli operators to the full cache. -/
theorem generatedSixth_partial_pauli_transport (k : Fin 9) (j : Fin 12) :
    spinConjugation (generatedSixthPartialSpinWord k) (generatedSixthSpinPauliCache j 0) =
      generatedSixthSpinPauliCache j k := by
  rcases generatedSixth_spin_pauli_cache_certificate j with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  have hp (q : Q) : spinConjugation (monsterSourcePermutationSpin 0) q =
      generatedSixthQGenerator 0 q := by
    exact monsterSourcePermutationSpin_conjugation _ q
  have hq (q : Q) : spinConjugation (monsterSourcePermutationSpin 1) q =
      generatedSixthQGenerator 1 q := by
    exact monsterSourcePermutationSpin_conjugation _ q
  have hx (q : Q) : spinConjugation xiSpinHolomorph q = generatedSixthQGenerator 2 q := by
    exact xiSpinHolomorph_conjugation q
  exact prefix_transport (monsterSourcePermutationSpin 0) (monsterSourcePermutationSpin 1)
    xiSpinHolomorph (fun i => generatedSixthSpinPauliCache j i)
    ((hp _).trans h1.symm) ((hx _).trans h2.symm) ((hp _).trans h3.symm)
    ((hq _).trans h4.symm) ((hp _).trans h5.symm) ((hx _).trans h6.symm)
    ((hq _).trans h7.symm) ((hx _).trans h8.symm) k

private theorem transported_fixed (s : SpinHolomorph) (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f) :
    spinRepresentation (spinConjugation s q) (s.val f) = s.val f := by
  rw [spinConjugation_representation]
  simp only [LinearEquiv.mul_apply]
  change s.val (spinRepresentation q (s.val.symm (s.val f))) = _
  rw [LinearEquiv.symm_apply_apply, hf]

/-- All twelve actual operators fix the genuine state at their original prefix. -/
theorem generatedSixth_partial_pauli_fixed (k : Fin 9) (j : Fin 12) :
    spinRepresentation (generatedSixthSpinPauliCache j k) (generatedSixthPartialSpinState k) =
      generatedSixthPartialSpinState k := by
  rw [← generatedSixth_partial_pauli_transport]
  exact transported_fixed (generatedSixthPartialSpinWord k) (generatedSixthSpinPauliInitial j)
    (generatedOddSpinState 0 1 0) (generatedSixth_spin_pauli_initial_fixed j)

/-- The anchored phase model is the genuine original state, with its actual anchor coefficient. -/
theorem generatedSixth_partial_phase_model (k : Fin 9) (t : SpinIndex) :
    generatedSixthPartialSpinState k t =
      (if generatedSixthAffineModulationMatrix (generatedSixthPartialPure k) *ᵥ
          (t + golayLabelCoefficients (generatedSixthPartialAnchor k)) = 0 then
        qSign (spinPhase (generatedSixthAffinePauliProduct
          (fun j => generatedSixthSpinPauliCache j k)
          (generatedSixthPartialProjection k *ᵥ
            (t + golayLabelCoefficients (generatedSixthPartialAnchor k))))
          (golayLabelCoefficients (generatedSixthPartialAnchor k))) else 0) *
      generatedSixthPartialSpinState k
        (golayLabelCoefficients (generatedSixthPartialAnchor k)) := by
  apply generatedSixth_affine_phase_model
    (C := generatedSixthPartialComplement k)
    (hq := generatedSixth_partial_pauli_fixed k)
  · intro j
    exact generatedSixth_affine_product_fixed _ _
      (generatedSixth_partial_pauli_fixed k) _
  · exact (generatedSixth_partial_pure_certificate k).1
  · exact (generatedSixth_partial_pure_certificate k).2
  · exact generatedSixth_partial_projection_certificate k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
