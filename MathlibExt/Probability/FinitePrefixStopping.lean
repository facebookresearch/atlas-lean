/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FinitePrefix

/-!
# EOS finite-string mass conservation

The ordinary alphabet is a finite type `Token`. A next-step kernel is
`q : List Token → PMF (Option Token)`: at an ordinary prefix `w` it gives a
normalized law on `Option Token`, where `none` is EOS (end of string) and
`some a` is the ordinary token `a`. There is no hypothesis that EOS has
positive mass: `q w none` may be `0`, `1`, or anything in between, and may
depend on the whole prefix `w`.

This file defines the defective survival and termination masses of finite
strings directly. The mass that never terminates is not renormalized away
and no infinite-trajectory constructor is introduced: the total mass of
terminated finite strings is `≤ 1`, not `1` in general. Bridge theorems
relate terminated mass to the normalized prefix law `FinitePrefix.law`
applied to the EOS-lifted kernel `eosLift q`.
-/

open scoped ENNReal

@[expose] public section

namespace MathlibExt.Probability.FinitePrefix


section EOS

variable {Token : Type*} [Fintype Token]

/-- EOS probability at an ordinary prefix.
No positivity is assumed. -/
noncomputable def eosProb (q : List Token → PMF (Option Token))
    (w : List Token) : ℝ≥0∞ :=
  q w Option.none

/-- Defective product of ordinary-token
masses along a word, in word order. For `a :: w` this is
`q [] (some a)` times the same product for `w` under the kernel shifted
by `a`. Unlike production `prefixProd`, the factors at each step sum
(over `a`) to `1 - q [] none`, so this is a subprobability product. -/
noncomputable def survivalProd (q : List Token → PMF (Option Token)) :
    List Token → ℝ≥0∞
  | [] => 1
  | a :: w => q [] (Option.some a) * survivalProd (fun p => q (a :: p)) w

/-- Mass of the terminated finite string
`w`, **including its final EOS**: the probability of emitting exactly
the ordinary tokens of `w`, in order, and then EOS at prefix `w`.
This is a mass on finite strings only; it is not a PMF on all strings,
and the missing (nonterminating) mass is not renormalized into it. -/
noncomputable def terminatedMass (q : List Token → PMF (Option Token))
    (w : List Token) : ℝ≥0∞ :=
  survivalProd q w * eosProb q w

/-- Survival mass `s n q`, the total
defective mass of ordinary words of length exactly `n`, i.e. the
probability of not having emitted EOS in the first `n` steps.
`s 0 q = 1` by definition (the empty word has been reached). Defined
by recursion on the horizon with the kernel shifted by each first
token, not by an infinite-path construction. -/
noncomputable def survivalMass (q : List Token → PMF (Option Token)) :
    ℕ → ℝ≥0∞
  | 0 => 1
  | n + 1 =>
      Finset.sum Finset.univ
        (fun a => q [] (Option.some a)
          * survivalMass (fun p => q (a :: p)) n)

/-- Termination mass `stop n q`, the total
mass of terminated finite strings of ordinary length exactly `n`, i.e.
the probability of emitting EOS for the first time at step `n + 1`,
after exactly `n` ordinary tokens. In particular
`stop 0 q = q [] none` is the mass of the empty terminated string. -/
noncomputable def stopMass (q : List Token → PMF (Option Token)) :
    ℕ → ℝ≥0∞
  | 0 => eosProb q []
  | n + 1 =>
      Finset.sum Finset.univ
        (fun a => q [] (Option.some a)
          * stopMass (fun p => q (a :: p)) n)

/-- Total mass of all terminated finite
strings, as a sum over all finite lengths. In general this is a
subprobability (`<= 1`); see `total_terminatedMass_le_one`. It is not
renormalized to `1`, and no infinite trajectory carries the remainder. -/
noncomputable def totalTerminatedMass
    (q : List Token → PMF (Option Token)) : ℝ≥0∞ :=
  ∑' n : ℕ, stopMass q n

/-- EOS-lift of `q` to a kernel on
`List (Option Token)`, used **only** to state the bridge to the
existing prefix `law`. On a prefix consisting only of `some` tokens it
agrees with `q` at the corresponding ordinary prefix (EOS cannot occur
in such a prefix). The values on prefixes already containing `none`
(by dropping it via `filterMap`) are irrelevant for every bridge
statement below and are not a trajectory semantics. -/
noncomputable def eosLift (q : List Token → PMF (Option Token)) :
    List (Option Token) → PMF (Option Token) :=
  fun u => q (u.filterMap (fun x => x))

/-- `survivalProd` on the empty word is `1`. -/
theorem survivalProd_nil (q : List Token → PMF (Option Token)) :
    survivalProd q ([] : List Token) = 1 := by
  rfl

/-- One-step unfolding of `survivalProd`. -/
theorem survivalProd_cons (q : List Token → PMF (Option Token))
    (a : Token) (w : List Token) :
    survivalProd q (a :: w)
      = q [] (Option.some a) * survivalProd (fun p => q (a :: p)) w := by
  rfl

/-- Terminated mass of the empty string is the EOS mass at `[]`. -/
theorem terminatedMass_nil (q : List Token → PMF (Option Token)) :
    terminatedMass q ([] : List Token) = eosProb q [] := by
  simp [terminatedMass, survivalProd]

/-- One-step unfolding of terminated mass, final EOS included. -/
theorem terminatedMass_cons (q : List Token → PMF (Option Token))
    (a : Token) (w : List Token) :
    terminatedMass q (a :: w)
      = q [] (Option.some a) * terminatedMass (fun p => q (a :: p)) w := by
  simp [terminatedMass, survivalProd, eosProb, mul_assoc]

/-- Survival at horizon zero is one, `s 0 = 1`. -/
theorem survivalMass_zero (q : List Token → PMF (Option Token)) :
    survivalMass q 0 = 1 := by
  rfl

/-- One-step unfolding of survival mass. -/
theorem survivalMass_succ (n : ℕ) (q : List Token → PMF (Option Token)) :
    survivalMass q (n + 1)
      = Finset.sum Finset.univ
          (fun a => q [] (Option.some a)
            * survivalMass (fun p => q (a :: p)) n) := by
  rfl

/-- Termination mass at length zero is the empty-string EOS mass. -/
theorem stopMass_zero (q : List Token → PMF (Option Token)) :
    stopMass q 0 = eosProb q [] := by
  rfl

/-- One-step unfolding of termination mass. -/
theorem stopMass_succ (n : ℕ) (q : List Token → PMF (Option Token)) :
    stopMass q (n + 1)
      = Finset.sum Finset.univ
          (fun a => q [] (Option.some a)
            * stopMass (fun p => q (a :: p)) n) := by
  rfl

/-- Helper: `List` as `Option` of head-tail, for tsum reindexing. -/
private noncomputable def listOptionEquiv : Option (Token × List Token) ≃ List Token where
  toFun | none => [] | some (a, w) => a :: w
  invFun | [] => none | a :: w => some (a, w)
  left_inv | none => rfl | some (a, w) => rfl
  right_inv | [] => rfl | a :: w => rfl

private theorem listOptionEquiv_apply_none :
    listOptionEquiv none = ([] : List Token) := rfl

private theorem listOptionEquiv_apply_some (a : Token) (w : List Token) :
    listOptionEquiv (some (a, w)) = a :: w := rfl

/-- Helper: tsum over words of length zero is the value at `[]`. -/
private theorem tsum_length_zero_aux (F : List Token → ℝ≥0∞) :
    (∑' w : List Token, if w.length = 0 then F w else 0) = F [] := by
  have h : ∀ w : List Token, w ≠ [] →
      (if w.length = 0 then F w else 0) = 0 := by
    intro w hw
    have hlen : w.length ≠ 0 := by
      intro h0
      apply hw
      exact List.length_eq_zero_iff.mp h0
    simp [hlen]
  rw [tsum_eq_single [] h]
  simp

private theorem tsum_option_aux {β : Type*} (G : Option β → ℝ≥0∞) :
    (∑' o, G o) = G none + ∑' b, G (some b) := by
  have hre := Equiv.tsum_eq (Equiv.optionEquivSumPUnit.{0} β).symm G
  have hsplit := Summable.tsum_sum
    (f := fun x => G ((Equiv.optionEquivSumPUnit.{0} β).symm x))
    ENNReal.summable ENNReal.summable
  have h1 : ∀ b : β, G ((Equiv.optionEquivSumPUnit.{0} β).symm (Sum.inl b))
      = G (some b) := fun b => rfl
  have h2 : ∀ u : PUnit.{1}, G ((Equiv.optionEquivSumPUnit.{0} β).symm (Sum.inr u))
      = G none := fun u => rfl
  have hP : (∑' _ : PUnit.{1}, G none) = G none := by
    rw [tsum_fintype, Fintype.sum_unique]
  rw [← hre, hsplit, tsum_congr h1, tsum_congr h2, hP, add_comm]

private theorem tsum_length_succ_aux (F : List Token → ℝ≥0∞) (n : ℕ) :
    (∑' w : List Token, if w.length = n + 1 then F w else 0)
      = ∑ a : Token, ∑' w : List Token,
          if w.length = n then F (a :: w) else 0 := by
  have hreindex : (∑' w : List Token, if w.length = n + 1 then F w else 0)
      = ∑' o : Option (Token × List Token),
          if (listOptionEquiv o).length = n + 1 then F (listOptionEquiv o) else 0 := by
    exact (Equiv.tsum_eq listOptionEquiv _).symm
  have hcong : ∀ b : Token × List Token,
      (if (listOptionEquiv (some b)).length = n + 1 then F (listOptionEquiv (some b)) else 0)
      = (if (b.1 :: b.2).length = n + 1 then F (b.1 :: b.2) else 0) :=
    fun ⟨a, w⟩ => rfl
  rw [hreindex, tsum_option_aux, tsum_congr hcong,
    ENNReal.tsum_prod (f := fun a w => if (a :: w).length = n + 1 then F (a :: w) else 0)]
  have h0 : ([] : List Token).length ≠ n + 1 := by
    rw [List.length_nil]
    omega
  have hnone : (if (listOptionEquiv none).length = n + 1
      then F (listOptionEquiv none) else 0) = 0 :=
    ite_eq_right (show (listOptionEquiv none).length ≠ n + 1 from h0)
  rw [hnone, zero_add]
  have hfin : ∀ G : Token → ℝ≥0∞, (∑' a : Token, G a) = ∑ a : Token, G a := by
    intro G
    exact tsum_fintype _
  rw [hfin]
  apply Finset.sum_congr rfl
  intro a _
  apply tsum_congr
  intro w
  have hcond : ((a :: w).length = n + 1 ↔ w.length = n) := by
    rw [List.length_cons]
    omega
  simp only [hcond]

/-- Helper: `survivalProd` is the `law`-mass of the mapped word. -/
theorem survivalProd_eq_law_eosLift_map (q : List Token → PMF (Option Token))
    (w : List Token) :
    survivalProd q w = (law w.length (eosLift q)) (w.map Option.some) := by
  induction w generalizing q with
  | nil =>
      rw [survivalProd_nil]
      have hmap : (([] : List Token).map Option.some) = [] := rfl
      have hlen : (([] : List Token).length) = 0 := rfl
      rw [hmap, hlen, law_zero]
      simp
  | cons a w ih =>
      rw [survivalProd_cons]
      have hmap : ((a :: w).map Option.some)
          = Option.some a :: w.map Option.some := rfl
      have hlen : (a :: w).length = w.length + 1 := rfl
      rw [hmap, hlen, mass_cons]
      have hshift : (fun p : List (Option Token) => eosLift q (Option.some a :: p))
          = eosLift (fun p : List Token => q (a :: p)) := by
        funext p
        simp [eosLift, List.filterMap_cons]
      rw [hshift, ih]
      have he0 : eosLift q [] = q [] := rfl
      rw [he0]

/-- `stopMass` is the sum, over ordinary words of the given
length, of their terminated masses (final EOS included). -/
theorem stopMass_eq_tsum_terminated
    (q : List Token → PMF (Option Token)) (n : ℕ) :
    stopMass q n
      = ∑' w : List Token,
          if w.length = n then terminatedMass q w else 0 := by
  induction n generalizing q with
  | zero =>
      rw [stopMass_zero, tsum_length_zero_aux]
      exact (terminatedMass_nil q).symm
  | succ n ih =>
      rw [stopMass_succ n q, tsum_length_succ_aux]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro w
      by_cases hw : w.length = n
      · rw [ite_eq_left hw, ite_eq_left hw]
        exact (terminatedMass_cons q a w).symm
      · rw [ite_eq_right hw, ite_eq_right hw, mul_zero]

/-- `survivalMass` is the sum, over ordinary words of the given
length, of their defective ordinary-token products. -/
theorem survivalMass_eq_tsum_survivalProd
    (q : List Token → PMF (Option Token)) (n : ℕ) :
    survivalMass q n
      = ∑' w : List Token,
          if w.length = n then survivalProd q w else 0 := by
  induction n generalizing q with
  | zero =>
      rw [survivalMass_zero, tsum_length_zero_aux]
      exact (survivalProd_nil q).symm
  | succ n ih =>
      rw [survivalMass_succ n q, tsum_length_succ_aux]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro w
      by_cases hw : w.length = n
      · rw [ite_eq_left hw, ite_eq_left hw]
        exact (survivalProd_cons q a w).symm
      · rw [ite_eq_right hw, ite_eq_right hw, mul_zero]

/-- Bridge to the existing prefix law: the terminated mass of `w`,
final EOS included, is the horizon-`(length w + 1)` `law`-mass of the
EOS-terminated word `w.map some ++ [none]` under the lifted kernel.
Every proper prefix of that word contains no EOS, so no EOS is ever
fed back as an ordinary token here. -/
theorem terminatedMass_eq_law_eosLift
    (q : List Token → PMF (Option Token)) (w : List Token) :
    terminatedMass q w
      = (law (w.length + 1) (eosLift q))
          (w.map Option.some ++ [Option.none]) := by
  induction w generalizing q with
  | nil =>
      rw [terminatedMass_nil]
      have hmap : (([] : List Token).map Option.some ++ [Option.none])
          = [Option.none] := rfl
      have hlen : (([] : List Token).length + 1) = 0 + 1 := rfl
      rw [hmap, hlen, mass_cons, law_zero]
      have he0 : eosLift q [] = q [] := rfl
      rw [he0]
      simp [eosProb]
  | cons a w ih =>
      rw [terminatedMass_cons]
      have hmap : ((a :: w).map Option.some ++ [Option.none])
          = Option.some a :: (w.map Option.some ++ [Option.none]) := rfl
      have hlen : (a :: w).length + 1 = (w.length + 1) + 1 := rfl
      rw [hmap, hlen, mass_cons]
      have hshift : (fun p : List (Option Token) => eosLift q (Option.some a :: p))
          = eosLift (fun p : List Token => q (a :: p)) := by
        funext p
        simp [eosLift, List.filterMap_cons]
      rw [hshift, ih]
      have he0 : eosLift q [] = q [] := rfl
      rw [he0]

/-- Bridge to the existing prefix law: survival mass is the sum of
horizon-`n` `law`-masses of the EOS-free words `w.map some`, over all
ordinary words `w` of length `n`, under the lifted kernel. -/
theorem survivalMass_eq_tsum_law_eosLift
    (q : List Token → PMF (Option Token)) (n : ℕ) :
    survivalMass q n
      = ∑' w : List Token,
          if w.length = n
            then (law n (eosLift q)) (w.map Option.some)
            else 0 := by
  rw [survivalMass_eq_tsum_survivalProd]
  apply tsum_congr
  intro w
  by_cases hw : w.length = n
  · rw [ite_eq_left hw, ite_eq_left hw, ← hw]
    exact survivalProd_eq_law_eosLift_map q w
  · rw [ite_eq_right hw, ite_eq_right hw]

/-- One-step stopping balance at every length,
`stop_n + s_(n+1) = s_n`. This is the inductive step behind
`stopping_mass_balance`: at each reached prefix, the normalized
`Option Token` law splits into EOS mass plus ordinary-token mass, with
no EOS positivity assumed. -/
theorem stop_add_survival_succ
    (q : List Token → PMF (Option Token)) (n : ℕ) :
    stopMass q n + survivalMass q (n + 1) = survivalMass q n := by
  induction n generalizing q with
  | zero =>
      have hnorm := PMF.tsum_coe (q [])
      rw [tsum_fintype] at hnorm
      rw [Fintype.sum_option] at hnorm
      simp only [stopMass_zero, survivalMass_zero, survivalMass_succ, eosProb,
        mul_one] at *
      exact hnorm
  | succ n ih =>
      rw [stopMass_succ n q, survivalMass_succ (n + 1) q, survivalMass_succ n q]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← mul_add, ih]

/-- Survival mass never exceeds one. -/
theorem survivalMass_le_one (q : List Token → PMF (Option Token))
    (n : ℕ) :
    survivalMass q n ≤ 1 := by
  induction n generalizing q with
  | zero => simp [survivalMass_zero]
  | succ n ih =>
      rw [survivalMass_succ n q]
      have hnorm := PMF.tsum_coe (q [])
      rw [tsum_fintype] at hnorm
      rw [Fintype.sum_option] at hnorm
      have hsum_le : ∑ a : Token, q [] (Option.some a) ≤ 1 := by
        calc ∑ a : Token, q [] (Option.some a)
            ≤ q [] Option.none + ∑ a : Token, q [] (Option.some a) :=
              le_add_left le_rfl
          _ = 1 := hnorm
      calc Finset.sum Finset.univ
              (fun a => q [] (Option.some a)
                * survivalMass (fun p => q (a :: p)) n)
          ≤ ∑ a : Token, q [] (Option.some a) := by
            apply Finset.sum_le_sum
            intro a _
            calc q [] (Option.some a) * survivalMass (fun p => q (a :: p)) n
                ≤ q [] (Option.some a) * 1 :=
                  mul_le_mul_right (ih (fun p => q (a :: p))) _
              _ = q [] (Option.some a) := mul_one _
        _ ≤ 1 := hsum_le

/-- Survival mass is antitone in the horizon. -/
theorem survivalMass_antitone (q : List Token → PMF (Option Token)) :
    Antitone (fun n => survivalMass q n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := stop_add_survival_succ q n
  calc survivalMass q (n + 1)
      ≤ stopMass q n + survivalMass q (n + 1) := le_add_left le_rfl
    _ = survivalMass q n := h

/-- Partial mass balance. The mass of all terminated strings of
length `< N`, plus the mass of surviving to length `N`, is exactly
one: nothing is lost and nothing is renormalized at any finite
horizon. -/
theorem partial_mass_balance (q : List Token → PMF (Option Token))
    (N : ℕ) :
    Finset.sum (Finset.range N) (fun k => stopMass q k)
      + survivalMass q N = 1 := by
  induction N generalizing q with
  | zero => simp [survivalMass_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc, stop_add_survival_succ]
      exact ih q

/-- Every finite partial terminated mass is at most one. -/
theorem partial_terminatedMass_le_one
    (q : List Token → PMF (Option Token)) (N : ℕ) :
    Finset.sum (Finset.range N) (fun k => stopMass q k) ≤ 1 := by
  have h := partial_mass_balance q N
  calc Finset.sum (Finset.range N) (fun k => stopMass q k)
      ≤ Finset.sum (Finset.range N) (fun k => stopMass q k)
          + survivalMass q N := le_add_right le_rfl
    _ = 1 := h

/-- Total finite-string mass is a subprobability, `<= 1`. The
defect `1 - totalTerminatedMass q` is the never-terminating mass; it
is not assigned to any finite string or infinite trajectory. -/
theorem total_terminatedMass_le_one
    (q : List Token → PMF (Option Token)) :
    totalTerminatedMass q ≤ 1 := by
  unfold totalTerminatedMass
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  simpa using partial_terminatedMass_le_one q n

/-- EOS finite-string mass conservation, packaged at an arbitrary length
`n` for an arbitrary finite ordinary alphabet and an arbitrary
prefix-dependent EOS kernel, with no EOS positivity assumed:

* `s 0 = 1`;
* `stop_n + s_(n+1) = s_n` (one-step balance);
* partial balance: terminated mass of lengths `<= n` plus survival to
  length `n + 1` is `1`;
* total mass of all terminated finite strings is `<= 1`.

No renormalization of the missing mass and no infinite-trajectory
constructor is used. -/
theorem stopping_mass_balance (q : List Token → PMF (Option Token))
    (n : ℕ) :
    survivalMass q 0 = 1
      ∧ stopMass q n + survivalMass q (n + 1) = survivalMass q n
      ∧ Finset.sum (Finset.range (n + 1)) (fun k => stopMass q k)
          + survivalMass q (n + 1) = 1
      ∧ totalTerminatedMass q ≤ 1 := by
  exact ⟨survivalMass_zero q, stop_add_survival_succ q n,
    partial_mass_balance q (n + 1), total_terminatedMass_le_one q⟩

end EOS

end MathlibExt.Probability.FinitePrefix
