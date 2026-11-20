/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.RSW.ExpDecayUpgrade
import Code.RSW.P5Equivalences

open Real Filter

namespace StatMech

namespace RSW

namespace P4ImpliesP5

open StatMech.RSW.Box






def rp4_StretchedExpDecay (a : ℕ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))




def rp4_ExpDecay (a : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, a n ≤ C * Real.exp (-c * n)






def rp4_P4 (a : ℕ → ℝ) : Prop := ¬ rp4_ExpDecay a









theorem rp4_expDecay_of_stretched (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hstr : rp4_StretchedExpDecay a) :
    rp4_ExpDecay a := by
  obtain ⟨α, hα, hbound⟩ := hstr
  obtain ⟨c, hc, C, hC, hdecay⟩ :=
    ExpDecay.rxd_exp_decay_of_stretched a hnn hle1 hanti α hα hbound hsub
  exact ⟨c, hc, C, hC, hdecay⟩






theorem rp4_not_stretched_of_P4 (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hP4 : rp4_P4 a) :
    ¬ rp4_StretchedExpDecay a :=
  fun hstr => hP4 (rp4_expDecay_of_stretched a hnn hle1 hanti hsub hstr)




















theorem rp4_p4_implies_p5 (a : ℕ → ℝ)
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))) → ℝ}
    {lam : ℕ → Set (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))) → ℝ}
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (hP4 : rp4_P4 a)
    (hdich : rp5_P5b ν ∨ rp4_StretchedExpDecay a)
    (hchain : ∀ (α : ℝ) (n : ℕ),
      ν 2 n (annulusEvent n) ≤ lam n (boxCrossingEvent α n)) :
    P5 lam := by
  
  have hnotstr : ¬ rp4_StretchedExpDecay a :=
    rp4_not_stretched_of_P4 a hnn hle1 hanti hsub hP4
  have hP5b : rp5_P5b ν := hdich.resolve_right hnotstr
  
  exact rp5_p5b_p5_lower hchain hP5b

end P4ImpliesP5

end RSW

end StatMech
