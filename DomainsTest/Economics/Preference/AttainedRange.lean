/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Preference.AttainedRange
import Mathlib.Tactic.Linarith

open MathlibExt.Economics Set

namespace DomainsTest.Economics.Preference.AttainedRange

noncomputable section

private def byUtility {X : Type*} (u : X → ℝ) : Preference X where
  R x y := u y ≤ u x
  complete _ _ := le_total _ _
  trans hxy hyz := hyz.trans hxy

private theorem represents_self {X : Type*} (u : X → ℝ) : (byUtility u).Represents u :=
  fun _ _ => Iff.rfl

-- The two alternatives `(n, false)` and `(n, true)` tie for each `n`. Squaring changes the
-- equally spaced attained scores 0, 1, 2 to 0, 1, 4, so the reparametrization is not affine.
private def score (x : ℕ × Bool) : ℝ := x.1

example : ∃ e : range score ≃o range (fun x => score x ^ 2),
    ∀ (n : ℕ) (b : Bool), (e (rangeFactorization score (n, b)) : ℝ) = (n : ℝ) ^ 2 := by
  let square (a : range score) : ℝ := (a : ℝ) ^ 2
  have hs : StrictMono square := by
    intro a b hab
    obtain ⟨x, hx⟩ := a.property
    have ha : 0 ≤ (a : ℝ) := hx ▸ Nat.cast_nonneg x.1
    exact pow_lt_pow_left₀ (show (a : ℝ) < b from hab) ha (by decide)
  obtain ⟨e, he⟩ := (represents_self score).exists_rangeOrderIso
    ((represents_self score).comp_rangeFactorization hs)
  exact ⟨e, fun n b => congrArg Subtype.val (he (n, b))⟩

-- No alternative is available from which to choose a default representative.
example (P : Preference Empty) (u v : Empty → ℝ) :
    ∃ e : range u ≃o range v, ∀ x, e (rangeFactorization u x) = rangeFactorization v x := by
  have hu : P.Represents u := fun x => nomatch x
  exact hu.exists_rangeOrderIso (fun x => nomatch x)

example (a b : ℝ) : ∃ e : range (fun _ : Unit => a) ≃o range (fun _ : Unit => b),
    (e ⟨a, ⟨(), rfl⟩⟩ : ℝ) = b := by
  have hv : (byUtility (fun _ : Unit => a)).Represents (fun _ => b) := fun _ _ =>
    ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  obtain ⟨e, he⟩ := (represents_self _).exists_rangeOrderIso hv
  exact ⟨e, congrArg Subtype.val (he ())⟩

-- Open a gap by shifting every nonnegative input up by one, leaving negative inputs fixed.
private def gap (x : ℝ) : ℝ := if x < 0 then x else x + 1

example : (∃ e : range gap ≃o range (id : ℝ → ℝ),
    ∀ x, e (rangeFactorization gap x) = rangeFactorization id x) ∧
    ¬ ∃ g : ℝ → ℝ, StrictMono g ∧ Function.LeftInverse g gap := by
  constructor
  · have hgap : StrictMono gap := by
      intro x y hxy
      unfold gap
      split_ifs <;> linarith
    have hu : (byUtility (id : ℝ → ℝ)).Represents gap := (represents_self id).comp_strictMono hgap
    exact hu.exists_rangeOrderIso (represents_self id)
  · rintro ⟨g, hg, h⟩
    -- `g 1 = 0` forces `g 0 < 0`, but a left inverse fixes every negative real, including `g 0`.
    have h1 : g 1 = 0 := by simpa [gap] using h 0
    have hneg : g 0 < 0 := (hg zero_lt_one).trans_eq h1
    have hfix : g (g 0) = g 0 := by simpa [gap, hneg] using h (g 0)
    exact (hg hneg).ne hfix

end

end DomainsTest.Economics.Preference.AttainedRange
