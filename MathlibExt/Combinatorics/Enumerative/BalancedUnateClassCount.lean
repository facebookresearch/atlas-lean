/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean
import Mathlib.Data.Set.Card
import MathlibExt.Combinatorics.Enumerative.SelfDualMonotoneBoolean

/-!
# Equivalence classes of balanced unate and monotone Boolean functions

Flipping the decreasing inputs of a unate function gives a monotone function of the same
weight. Thus restricting each balanced unate class to its monotone members gives the
same count for both NN and NPN equivalence.

## References

* Aniruddha Biswas and Palash Sarkar, *Counting Unate and Monotone Boolean Functions Under
  Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer Sequences 28 (2025),
  Article 25.3.4, pp. 1–19, Proposition 14(b), p. 11.
  <https://cs.uwaterloo.ca/journals/JIS/VOL28/Biswas/biswas6.pdf>
-/

namespace MetaMathlibExt

open Function

variable {n : ℕ}

private def flipInputs (a x : Fin n → Bool) (i : Fin n) : Bool := xor (x i) (a i)

private theorem flipInputs_update (a x : Fin n → Bool) (i : Fin n) (b : Bool) :
    flipInputs a (update x i b) = update (flipInputs a x) i (xor b (a i)) := by
  funext j
  by_cases h : j = i <;> simp [flipInputs, h]

private theorem boolFunWeight_comp_flipInputs (f : (Fin n → Bool) → Bool) (a : Fin n → Bool) :
    boolFunWeight (f ∘ flipInputs a) = boolFunWeight f := by
  have hinv : Involutive (flipInputs a) := by
    intro x
    funext i
    simp [flipInputs]
  apply Finset.card_equiv (hinv.toPerm _)
  intro x
  simp [Involutive.coe_toPerm]

/-- Flip precisely the coordinates in which `f` is not increasing. -/
private theorem exists_monotone_comp_flipInputs {f : (Fin n → Bool) → Bool}
    (hf : IsUnateBoolFun f) : ∃ a : Fin n → Bool, Monotone (f ∘ flipInputs a) := by
  classical
  let a (i : Fin n) := decide (¬ IsBoolFunIncreasingIn f i)
  refine ⟨a, monotone_of_le_update fun x i hx => ?_⟩
  simp only [comp_apply, flipInputs_update]
  by_cases hi : IsBoolFunIncreasingIn f i
  · simpa [a, hi] using hi (flipInputs a x) (by simp [flipInputs, a, hi, hx])
  · have hy : flipInputs a x i = true := by simp [flipInputs, a, hi, hx]
    have he : update (flipInputs a x) i true = flipInputs a x := by rw [← hy, update_eq_self]
    have hedge := ((hf i).resolve_left hi) (update (flipInputs a x) i false) (by simp)
    rw [update_idem, he] at hedge
    simpa [a, hi] using hedge

private theorem nnEquivalence : Equivalence (IsBoolFunNNEquiv (n := n)) where
  refl := isBoolFunNNEquiv_refl
  symm := by
    rintro f g ⟨a, c, h⟩
    refine ⟨a, c, fun x => ?_⟩
    rw [h]
    simp
  trans := by
    rintro f g k ⟨a, c, hfg⟩ ⟨b, d, hgk⟩
    refine ⟨fun i => xor (b i) (a i), xor c d, fun x => ?_⟩
    rw [hgk, hfg]
    simp only [Bool.xor_assoc]

private theorem npnEquivalence : Equivalence (IsBoolFunNPNEquiv (n := n)) where
  refl := isBoolFunNPNEquiv_refl
  symm := by
    rintro f g ⟨σ, a, c, h⟩
    refine ⟨σ.symm, fun i => a (σ.symm i), c, fun x => ?_⟩
    rw [h]
    simp
  trans := by
    rintro f g k ⟨σ, a, c, hfg⟩ ⟨τ, b, d, hgk⟩
    refine ⟨σ.trans τ, fun i => xor (b (σ i)) (a i), xor c d, fun x => ?_⟩
    rw [hgk, hfg]
    simp only [Equiv.trans_apply, Bool.xor_assoc]

/-- If `Q` is contained in `P` and meets each `P`-class, intersection with `Q` is a bijection. -/
private theorem classCount_eq_of_restriction
    {R : ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool) → Prop}
    (hR : Equivalence R) {P Q : ((Fin n → Bool) → Bool) → Prop}
    (hQP : ∀ f, Q f → P f) (hrep : ∀ f, P f → ∃ g, Q g ∧ R f g) :
    boolFunClassCount R P = boolFunClassCount R Q := by
  have hclass {B : ((Fin n → Bool) → Bool) → Prop} {f g} (hfg : R f g) :
      {k | B k ∧ R f k} = {k | B k ∧ R g k} :=
    Set.ext fun _ => and_congr_right fun _ => ⟨hR.trans (hR.symm hfg), hR.trans hfg⟩
  have hrestrict (f : (Fin n → Bool) → Bool) :
      {g | P g ∧ R f g} ∩ {g | Q g} = {g | Q g ∧ R f g} :=
    Set.ext fun _ => ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hQP _ h.1, h.2⟩, h.1⟩⟩
  change {S : Set _ | ∃ f, P f ∧ S = {g | P g ∧ R f g}}.ncard =
    {S : Set _ | ∃ f, Q f ∧ S = {g | Q g ∧ R f g}}.ncard
  refine Set.ncard_congr (fun S _ => S ∩ {g | Q g}) ?_ ?_ ?_
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hfg⟩ := hrep f hf
    exact ⟨g, hg, (hrestrict f).trans (hclass hfg)⟩
  · rintro _ _ ⟨f, hf, rfl⟩ ⟨g, _, rfl⟩ heq
    rw [hrestrict, hrestrict] at heq
    -- A member of the common restriction witnesses that the original classes agree.
    obtain ⟨k, hk, hfk⟩ := hrep f hf
    have hmem : k ∈ {l | Q l ∧ R f l} := ⟨hk, hfk⟩
    rw [heq] at hmem
    exact hclass (hR.trans hfk (hR.symm hmem.2))
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hQP f hf, rfl⟩, hrestrict f⟩

/-- **Balanced unate and balanced monotone functions have equally many NN- and NPN-classes.**
For every $n$, call an $n$-variable Boolean function $f$ balanced when $2\,\mathrm{wt}(f) = 2^n$,
where $\mathrm{wt}(f)$ is the weight of $f$. The number of NN-inequivalent balanced unate
$n$-variable Boolean functions equals the number of NN-inequivalent balanced monotone ones, and
the number of NPN-inequivalent balanced unate $n$-variable Boolean functions equals the number of
NPN-inequivalent balanced monotone ones. Here monotone means nondecreasing for the coordinatewise
order with $0 < 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14(b) (`jis-2025-25.3.4-prop-14`). -/
public theorem boolFunClassCount_balanced_unate_eq_monotone (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunNNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
        = boolFunClassCount (n := n) IsBoolFunNNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) ∧
      boolFunClassCount (n := n) IsBoolFunNPNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
        = boolFunClassCount (n := n) IsBoolFunNPNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) := by
  let balanced (f : (Fin n → Bool) → Bool) : Prop := 2 * boolFunWeight f = 2 ^ n
  have hsub (f : (Fin n → Bool) → Bool) (hf : Monotone f ∧ balanced f) :
      IsUnateBoolFun f ∧ balanced f := ⟨isUnateBoolFun_of_monotone hf.1, hf.2⟩
  have hrep (f : (Fin n → Bool) → Bool) (hf : IsUnateBoolFun f ∧ balanced f) :
      ∃ g, (Monotone g ∧ balanced g) ∧ IsBoolFunNNEquiv f g := by
    obtain ⟨a, ha⟩ := exists_monotone_comp_flipInputs hf.1
    refine ⟨f ∘ flipInputs a, ⟨ha, ?_⟩, a, false, fun _ => (Bool.xor_false _).symm⟩
    simpa only [balanced, boolFunWeight_comp_flipInputs] using hf.2
  refine ⟨classCount_eq_of_restriction nnEquivalence hsub hrep,
    classCount_eq_of_restriction npnEquivalence hsub fun f hf => ?_⟩
  obtain ⟨g, hg, a, c, h⟩ := hrep f hf
  exact ⟨g, hg, 1, a, c, h⟩

end MetaMathlibExt
