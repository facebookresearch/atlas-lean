/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BaseRecognizable
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Cobham's gap theorem

This file proves Cobham's gap theorem for the recognizable-set API
`MetaMathlibExt.IsBaseRecognizable` from `MathlibExt.NumberTheory.BaseRecognizable`.

Source: T. Kärki, A. Lacroix, and M. Rigo, *On the Recognizability of
Self-Generating Sets*, Journal of Integer Sequences 13 (2010),
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex>.
Complete TeX SHA-256:
`df5d17d81e344c0c20304f1d98d35c7e263a67dcb043e6b62307fb793e4810d5`.
Recognizability definition lines 110–120, no-final-newline span SHA-256:
`bf0c0a1817a739be85df010f9aa344e0c32cf717290202a23c3ada75eac9a03d`.
Gap notation and theorem lines 979–995, no-final-newline span SHA-256:
`f968765f1533988a25b2111265bcd9cf0354f4d738e3f9440a1d18e086baee3b`.

The source writes an infinite ordered set as `X = {x₀ < x₁ < ...}` and says
either the limsup of `x_(i+1)/x_i` is greater than one or consecutive gaps
are uniformly bounded. `StrictMono x` makes `Set.range x` infinite and gives
its consecutive increasing enumeration. `ENNReal` is intentional so an
unbounded ratio limsup is `⊤`. If `x 0 = 0`, the index-zero ratio may be `⊤`;
it is a single finite-prefix term and does not affect the `atTop` limsup.
Natural subtraction is exact under strict monotonicity.
-/

section
namespace MetaMathlibExt

private def paddedDigits {k : ℕ} (hk : 2 ≤ k) (r n : ℕ) : List (Fin k) :=
  List.replicate (r - (baseDigits hk n).length) ⟨0, by omega⟩ ++ baseDigits hk n

private lemma baseDigits_length_le {k : ℕ} (hk : 2 ≤ k) {r n : ℕ}
    (hn : n < k ^ r) : (baseDigits hk n).length ≤ r := by
  rw [baseDigits_length]
  by_cases hn0 : n = 0
  · subst n
    simp
  · rw [Nat.length_digits k n (by omega) hn0]
    have := (Nat.log_lt_iff_lt_pow (by omega) hn0).2 hn
    omega

private lemma paddedDigits_length {k : ℕ} (hk : 2 ≤ k) {r n : ℕ}
    (hn : n < k ^ r) : (paddedDigits hk r n).length = r := by
  have hlen := baseDigits_length_le hk hn
  simp [paddedDigits, Nat.sub_add_cancel hlen]

private lemma baseWordValue_replicate_zero {k r : ℕ} (hk : 2 ≤ k) :
    baseWordValue (List.replicate r (⟨0, by omega⟩ : Fin k)) = 0 := by
  induction r with
  | zero => simp [baseWordValue]
  | succ r ih =>
    rw [List.replicate_succ]
    simpa [baseWordValue] using ih

private lemma paddedDigits_value {k : ℕ} (hk : 2 ≤ k) (r n : ℕ) :
    baseWordValue (paddedDigits hk r n) = n := by
  rw [paddedDigits, baseWordValue_append, baseWordValue_replicate_zero hk,
    zero_mul, zero_add, baseWordValue_baseDigits]

/-- **Cobham's gap theorem without a separate base hypothesis.** Let $k$ be a natural number and
let $x_0 < x_1 < x_2 < \cdots$ be a strictly increasing sequence of natural numbers whose set of
values is recognizable in base $k$. Then either the limit superior, as $i \to \infty$, of the
ratios $x_{i+1} / x_i$ computed in the extended nonnegative reals $[0, \infty]$ (where a ratio
with denominator $0$ is $\infty$) is greater than $1$, or there is a natural number $C$ with
$x_{i+1} - x_i \le C$ for every $i$.

Recognizability in base $k$ already requires $k \ge 2$, so no separate hypothesis on $k$ is
needed. -/
theorem cobham_gap_theorem_general {k : ℕ} {x : ℕ → ℕ}
    (hx : StrictMono x)
    (hX : IsBaseRecognizable k (Set.range x)) :
    Filter.limsup
      (fun i => ((x (i + 1) : ENNReal) / (x i : ENNReal)))
    Filter.atTop > 1 ∨
    ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C := by
  classical
  have hk : 2 ≤ k := hX.1
  by_cases hbounded : ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C
  · exact Or.inr hbounded
  left
  have hgap : ∀ C : ℕ, ∃ i : ℕ, C < x (i + 1) - x i := by
    simpa only [not_exists, not_forall, not_le] using hbounded
  rcases hX with ⟨_, q, hq, init, transition, accept, haccept⟩
  let gapIndex : ℕ → ℕ := fun r ↦ Classical.choose (hgap (2 * k ^ r))
  have hgapIndex (r : ℕ) :
      2 * k ^ r < x (gapIndex r + 1) - x (gapIndex r) :=
    Classical.choose_spec (hgap (2 * k ^ r))
  let blockPrefix : ℕ → ℕ := fun r ↦ x (gapIndex r) / k ^ r + 1
  have hpow (r : ℕ) : 0 < k ^ r := pow_pos (by omega) r
  have hprefix (r : ℕ) : 0 < blockPrefix r := by simp [blockPrefix]
  have hblock (r n : ℕ)
      (hnl : blockPrefix r * k ^ r ≤ n)
      (hnr : n < (blockPrefix r + 1) * k ^ r) : n ∉ Set.range x := by
    intro hn
    obtain ⟨j, rfl⟩ := hn
    have hleft : x (gapIndex r) < blockPrefix r * k ^ r := by
      change x (gapIndex r) < (x (gapIndex r) / k ^ r + 1) * k ^ r
      simpa [Nat.add_mul] using
        (Nat.lt_div_mul_add (a := x (gapIndex r)) (b := k ^ r) (hpow r))
    have hgap' : x (gapIndex r) + 2 * k ^ r < x (gapIndex r + 1) := by
      simpa [Nat.add_comm] using
        (Nat.lt_sub_iff_add_lt.mp (hgapIndex r))
    have hright : (blockPrefix r + 1) * k ^ r ≤ x (gapIndex r + 1) := by
      change (x (gapIndex r) / k ^ r + 1 + 1) * k ^ r ≤
        x (gapIndex r + 1)
      calc
        (x (gapIndex r) / k ^ r + 1 + 1) * k ^ r =
            x (gapIndex r) / k ^ r * k ^ r + 2 * k ^ r := by ring
        _ ≤ x (gapIndex r) + 2 * k ^ r :=
          Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
        _ ≤ x (gapIndex r + 1) := hgap'.le
    have hjlow : gapIndex r < j := (hx.lt_iff_lt).mp (hleft.trans_le hnl)
    have hjhigh : j < gapIndex r + 1 :=
      (hx.lt_iff_lt).mp (hnr.trans_le hright)
    omega
  let state : ℕ → Fin q := fun r ↦
    (baseDigits hk (blockPrefix r)).foldl transition init
  obtain ⟨repeatedState, hrepeated⟩ := Finite.exists_infinite_fiber state
  have hrepeatedSet : Set.Infinite {r : ℕ | state r = repeatedState} := by
    have hi : Set.Infinite (state ⁻¹' {repeatedState}) :=
      Set.infinite_coe_iff.mp hrepeated
    convert hi using 1
    ext r
    simp
  obtain ⟨r₀, hr₀, _⟩ := hrepeatedSet.exists_gt 0
  let fixedPrefix := blockPrefix r₀
  have hfixedPrefix : 0 < fixedPrefix := hprefix r₀
  have hstate₀ : state r₀ = repeatedState := hr₀
  have hfixedBlock (r n : ℕ) (hr : state r = repeatedState)
      (hnl : fixedPrefix * k ^ r ≤ n)
      (hnr : n < (fixedPrefix + 1) * k ^ r) : n ∉ Set.range x := by
    intro hn
    let remainder := n - fixedPrefix * k ^ r
    have hremainder : remainder < k ^ r := by
      dsimp [remainder]
      rw [Nat.sub_lt_iff_lt_add hnl]
      simpa [Nat.add_mul, Nat.add_comm] using hnr
    let suffix := paddedDigits hk r remainder
    have hsuffixLength : suffix.length = r := paddedDigits_length hk hremainder
    have hsuffixValue : baseWordValue suffix = remainder := paddedDigits_value hk r remainder
    have hfixedValue :
        baseWordValue (baseDigits hk fixedPrefix ++ suffix) = n := by
      rw [baseWordValue_append, baseWordValue_baseDigits, hsuffixLength,
        hsuffixValue]
      exact Nat.add_sub_of_le hnl
    have horiginalValue :
        baseWordValue (baseDigits hk (blockPrefix r) ++ suffix) =
          blockPrefix r * k ^ r + remainder := by
      rw [baseWordValue_append, baseWordValue_baseDigits, hsuffixLength,
        hsuffixValue]
    have hfixedCanonical :
        IsCanonicalBaseWord (baseDigits hk fixedPrefix ++ suffix) :=
      (isCanonicalBaseWord_baseDigits hk fixedPrefix).append
        (baseDigits_ne_nil hk hfixedPrefix.ne')
    have horiginalCanonical :
        IsCanonicalBaseWord (baseDigits hk (blockPrefix r) ++ suffix) :=
      (isCanonicalBaseWord_baseDigits hk (blockPrefix r)).append
        (baseDigits_ne_nil hk (hprefix r).ne')
    have hstates :
        (baseDigits hk fixedPrefix ++ suffix).foldl transition init =
          (baseDigits hk (blockPrefix r) ++ suffix).foldl transition init := by
      simp only [List.foldl_append]
      have : state r₀ = state r := hstate₀.trans hr.symm
      simpa [state, fixedPrefix] using congrArg
        (fun s ↦ suffix.foldl transition s) this
    have haccepted :
        accept ((baseDigits hk fixedPrefix ++ suffix).foldl transition init) = true :=
      (haccept _).2 ⟨hfixedCanonical, hfixedValue ▸ hn⟩
    have horiginalAccepted :
        accept ((baseDigits hk (blockPrefix r) ++ suffix).foldl
          transition init) = true := by
      rw [← hstates]
      exact haccepted
    have horiginalMember : blockPrefix r * k ^ r + remainder ∈ Set.range x := by
      have hm := (haccept _).1 horiginalAccepted
      rw [horiginalValue] at hm
      exact hm.2
    apply hblock r (blockPrefix r * k ^ r + remainder)
      (Nat.le_add_right _ _) _ horiginalMember
    calc
      blockPrefix r * k ^ r + remainder <
          blockPrefix r * k ^ r + k ^ r := Nat.add_lt_add_left hremainder _
      _ = (blockPrefix r + 1) * k ^ r := by ring
  let ratioBound : ENNReal :=
    ((fixedPrefix + 1 : ℕ) : ENNReal) / (fixedPrefix : ENNReal)
  have hfixedCastZero : (fixedPrefix : ENNReal) ≠ 0 := by
    exact_mod_cast hfixedPrefix.ne'
  have hfixedCastTop : (fixedPrefix : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top fixedPrefix
  have hratioBound : 1 < ratioBound := by
    change 1 < ((fixedPrefix + 1 : ℕ) : ENNReal) / (fixedPrefix : ENNReal)
    rw [← ENNReal.div_self hfixedCastZero hfixedCastTop]
    apply ENNReal.div_lt_div_right hfixedCastZero hfixedCastTop
    exact_mod_cast Nat.lt_succ_self fixedPrefix
  have hfrequent :
      ∃ᶠ i : ℕ in Filter.atTop,
        ratioBound ≤ (x (i + 1) : ENNReal) / (x i : ENNReal) := by
    rw [Filter.frequently_atTop]
    intro bound
    obtain ⟨r, hr, hrlarge⟩ := hrepeatedSet.exists_gt (x bound)
    have hpowLarge : x bound < k ^ r :=
      hrlarge.trans (Nat.lt_pow_self (by omega))
    have hpowFixed : k ^ r ≤ fixedPrefix * k ^ r := by
      exact Nat.le_mul_of_pos_left (k ^ r) hfixedPrefix
    have hboundLeft : x bound < fixedPrefix * k ^ r :=
      hpowLarge.trans_le hpowFixed
    have hleftRight : fixedPrefix * k ^ r < (fixedPrefix + 1) * k ^ r := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self fixedPrefix) (hpow r)
    have htExists : ∃ t : ℕ, (fixedPrefix + 1) * k ^ r ≤ x t := by
      refine ⟨(fixedPrefix + 1) * k ^ r, ?_⟩
      exact hx.id_le _
    let t := Nat.find htExists
    have ht : (fixedPrefix + 1) * k ^ r ≤ x t := Nat.find_spec htExists
    have hxzero : x 0 < (fixedPrefix + 1) * k ^ r := by
      exact (hx.monotone (Nat.zero_le bound)).trans_lt
        (hboundLeft.trans hleftRight)
    have htpos : 0 < t := by
      dsimp [t]
      rw [Nat.find_pos]
      exact not_le_of_gt hxzero
    let i := t - 1
    have hit : i + 1 = t := Nat.sub_add_cancel htpos
    have hitlt : i < t := by omega
    have hiprev : x i < (fixedPrefix + 1) * k ^ r := by
      have hmin := Nat.find_min htExists (m := i) (by simpa [t] using hitlt)
      have := hmin
      omega
    have hileft : x i < fixedPrefix * k ^ r := by
      by_contra hi
      exact hfixedBlock r (x i) hr (Nat.le_of_not_gt hi) hiprev ⟨i, rfl⟩
    have hinext : (fixedPrefix + 1) * k ^ r ≤ x (i + 1) := by
      simpa [hit] using ht
    have hibound : bound ≤ i := by
      have : bound < i + 1 :=
        (hx.lt_iff_lt).mp (hboundLeft.trans hleftRight |>.trans_le hinext)
      omega
    refine ⟨i, hibound, ?_⟩
    have hkCastZero : (k ^ r : ENNReal) ≠ 0 := by
      exact_mod_cast (hpow r).ne'
    have hkCastTop : (k ^ r : ENNReal) ≠ ⊤ :=
      by simpa only [Nat.cast_pow] using ENNReal.natCast_ne_top (k ^ r)
    have hscaled :
        (((fixedPrefix + 1) * k ^ r : ℕ) : ENNReal) /
            ((fixedPrefix * k ^ r : ℕ) : ENNReal) = ratioBound := by
      simp only [ratioBound, Nat.cast_mul, Nat.cast_pow]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENNReal.mul_div_mul_right (fixedPrefix + 1 : ENNReal)
          (fixedPrefix : ENNReal) hkCastZero hkCastTop)
    rw [← hscaled]
    apply ENNReal.div_le_div
    · exact_mod_cast hinext
    · exact_mod_cast hileft.le
  exact hratioBound.trans_le
    (Filter.le_limsup_of_frequently_le hfrequent)

set_option linter.unusedVariables false in
/-- **Cobham's gap theorem.** Let $k \ge 2$ be a natural number and let $x_0 < x_1 < x_2 < \cdots$
be a strictly increasing sequence of natural numbers whose set of values is recognizable in base
$k$. Then either the limit superior, as $i \to \infty$, of the ratios $x_{i+1} / x_i$ computed in
the extended nonnegative reals $[0, \infty]$ (so an unbounded limit superior is $\infty$, and a
ratio with denominator $0$ is $\infty$) is greater than $1$, or there is a natural number $C$ with
$x_{i+1} - x_i \le C$ for every $i$.

Proves `Wanted` entry `cobham_gap_theorem`.

Source: Kärki–Lacroix–Rigo gap theorem, lines 979–995 of
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex>.
-/
theorem cobham_gap_theorem {k : ℕ} {x : ℕ → ℕ}
    (hx : StrictMono x)
    (hk : 2 ≤ k)
    (hX : IsBaseRecognizable k (Set.range x)) :
    Filter.limsup
      (fun i => ((x (i + 1) : ENNReal) / (x i : ENNReal)))
    Filter.atTop > 1 ∨
    ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C :=
  cobham_gap_theorem_general hx hX

end MetaMathlibExt
