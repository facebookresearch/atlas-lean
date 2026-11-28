/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelNonIntegrality
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The periodic Göbel sign sequence

For an even natural number $l$ and a natural number $s \le l$ with $2s+1$ coprime to $l+1$,
the two reflection laws and normalization at index one determine a unique periodic sign
sequence $b_{l,s}$. If also $l \ge 2$, the complementary sequences $b_{l,s}$ and $b_{l,l-s}$
agree off multiples of $l+1$ and have opposite signs at those multiples. Under the same
hypotheses, $b_{l,s}$ changes sign under a shift by $2s+1$ when neither index is a multiple of
$l+1$. If in addition $s < l/2$, it changes sign under a shift by $2t$ away from those multiples
and is symmetric about $t$ when neither reflected index is a multiple of $l+1$, where
$t = l/2-s$.

The first shift identity follows directly by composing the defining reflections, rather than
using the complementary sequence as in the published proof.

## References

* Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
  Journal of Integer Sequences **29** (2026), Article 26.3.8, pp. 1–25, Proposition 20 and
  Lemmas 22 and 23.
-/

namespace MetaMathlibExt
namespace existsUnique_gobelBSequence

private theorem exists_sequence (l s : ℕ) (hleven : Even l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1)) :
    ∃ b : ℤ → ℤ, IsGobelBSequence l s b := by
  -- Measure each residue in steps of −(2s+1), a generator modulo l+1.
  let u := ZMod.unitOfCoprime (2 * s + 1) hcoprime
  let r (n : ℤ) : ZMod (l + 1) := -(↑u⁻¹ * (n : ZMod (l + 1)))
  let b (n : ℤ) : ℤ := if (r n).val % 2 = (r 1).val % 2 then 1 else -1
  have hmod : ((l : ZMod (l + 1)) + 1) = 0 := by
    exact_mod_cast ZMod.natCast_self (l + 1)
  have hrperiod : Function.Periodic r (l + 1 : ℤ) := by
    intro n
    simp [r, Int.cast_add, hmod]
  obtain ⟨k, hk⟩ := hleven
  refine ⟨b, fun n => ?_, fun n => ?_, ?_, fun n hn => ?_, fun n => ?_⟩
  · simp only [b]
    split <;> simp
  · simp only [b, hrperiod n]
  · simp [b]
  · change n % (l + 1 : ℤ) ≠ 0 at hn
    have hn' : (n : ZMod (l + 1)) ≠ 0 := by
      simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero,
        Nat.cast_add, Nat.cast_one] using hn
    have hr : r n ≠ 0 := by simpa [r] using hn'
    have hneg : r ((l + 1 : ℤ) - n) = -r n := by simp [r, hmod]
    have hlt := (r n).val_lt
    simp only [b, hneg, ZMod.neg_val, ite_eq_right hr]
    split <;> split <;> omega
  · -- The second reflection sends coordinate x to −1−x, whose representative is l−x.val.
    have hu : (↑u⁻¹ : ZMod (l + 1)) * (2 * (s : ZMod (l + 1)) + 1) = 1 := by
      simp [u, ZMod.coe_unitOfCoprime]
    have href : r ((s : ℤ) + 1 + n) = -1 - r ((s : ℤ) - n) := by
      simp only [r, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
      linear_combination -hu
    have hlt := (r ((s : ℤ) - n)).val_lt
    have hle : (r ((s : ℤ) - n)).val ≤ (-1 : ZMod (l + 1)).val := by
      rw [ZMod.val_neg_one]
      omega
    have hparity : (r ((s : ℤ) + 1 + n)).val % 2 = (r ((s : ℤ) - n)).val % 2 := by
      rw [href, ZMod.val_sub hle, ZMod.val_neg_one]
      omega
    simp only [b, hparity]

private theorem unique_sequence {l s : ℕ} (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    {b c : ℤ → ℤ} (hb : IsGobelBSequence l s b) (hc : IsGobelBSequence l s c) : b = c := by
  -- Agreement is preserved by both reflections, hence by translation through 2s+1.
  let P (n : ℤ) := b n = c n
  have hp : Function.Periodic P (l + 1 : ℤ) := by
    intro n
    simp only [P, hb.2.1, hc.2.1]
  have hneg (n : ℤ) : P (-n) = P n := by
    by_cases hn : n % (l + 1 : ℤ) = 0
    · obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hn
      rw [hk, mul_comm]
      simpa only [Int.cast_id] using (hp.int_mul k).neg_eq.trans (hp.int_mul k).eq.symm
    · rw [← hp.sub_eq' (x := n)]
      change (_ = _) = (b n = c n)
      rw [hb.2.2.2.1 n hn, hc.2.2.2.1 n hn, neg_inj]
  have hstep : Function.Periodic P (2 * s + 1 : ℤ) := by
    intro n
    have reflect {f : ℤ → ℤ} (hf : IsGobelBSequence l s f) :
        f (n + (2 * s + 1 : ℤ)) = f (-n) := by
      convert (hf.2.2.2.2 ((s : ℤ) + n)).symm using 1 <;> congr 1 <;> ring
    change (b _ = c _) = (b n = c n)
    rw [reflect hb, reflect hc]
    exact hneg n
  obtain ⟨u, v, huv⟩ := hcoprime.isCoprime
  push_cast at huv
  have hp₁ : Function.Periodic P 1 := huv ▸ (hstep.int_mul u).add_period (hp.int_mul v)
  funext n
  have hn : P n = P 0 := by simpa only [mul_one, Int.cast_id] using hp₁.int_mul_eq n
  exact hn.mpr (hp₁.eq.mp (hb.2.2.1.trans hc.2.2.1.symm))

end existsUnique_gobelBSequence

set_option linter.unusedVariables false in
/-- **Existence and uniqueness of the sequence $b_{l,s}$.** Let $l$ be an even natural number and
$s$ a natural number with $s \le l$ such that $2s + 1$ and $l + 1$ are coprime. Then exactly one
function $b : \mathbb{Z} \to \mathbb{Z}$ satisfies the defining conditions of $b_{l,s}$:
$b(n) = \pm 1$ for every integer $n$, $b(n + l + 1) = b(n)$ for every $n$, $b(1) = 1$,
$b(n) = -b(l + 1 - n)$ for every $n$ not divisible by $l + 1$, and $b(s - n) = b(s + 1 + n)$ for
every $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on
Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article
26.3.8, Proposition 20. -/
public theorem existsUnique_gobelBSequence
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hcoprime : Nat.Coprime (2 * s + 1) (l + 1)) :
    ∃! b : ℤ → ℤ, IsGobelBSequence l s b := by
  obtain ⟨b, hb⟩ := existsUnique_gobelBSequence.exists_sequence l s hleven hcoprime
  exact ⟨b, hb, fun c hc => existsUnique_gobelBSequence.unique_sequence hcoprime hc hb⟩

/-- **Complementary sequences $b_{l,s}$ and $b_{l,l-s}$.** Let $l \ge 2$ be an even natural
number and $s \le l$ a natural number such that $2s + 1$ and $l + 1$ are coprime. Let
$b_1, b_2 : \mathbb{Z} \to \mathbb{Z}$ satisfy the defining conditions of $b_{l,s}$ and of
$b_{l,l-s}$ respectively. Then for every integer $n$, $b_1(n) = b_2(n)$ if $l + 1$ does not divide
$n$, and $b_1(n) = -b_2(n)$ if $l + 1$ divides $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 22. -/
public theorem gobelBSequence_complement
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hl2 : 2 ≤ l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    (b₁ b₂ : ℤ → ℤ) (hb₁ : IsGobelBSequence l s b₁)
    (hb₂ : IsGobelBSequence l (l - s) b₂) :
    ∀ n, (Int.emod n (l + 1 : ℤ) ≠ 0 → b₁ n = b₂ n) ∧
      (Int.emod n (l + 1 : ℤ) = 0 → b₁ n = -b₂ n) := by
  obtain ⟨hsign, hperiod, hone, hanti, hreflect⟩ := hb₂
  let L : ℤ := l + 1
  have hp : Function.Periodic b₂ L := hperiod
  have hneg (n : ℤ) (hn : n % L ≠ 0) : -b₂ (-n) = b₂ n := by
    rw [← hp.sub_eq' (x := n)]
    exact (hanti n hn).symm
  let c : ℤ → ℤ := fun n => -b₂ (-n)
  have hc : IsGobelBSequence l s c := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n
      rcases hsign (-n) with h | h
      · exact Or.inr (congrArg Neg.neg h)
      · exact Or.inl (by simp [c, h])
    · intro n
      change -b₂ (-(n + L)) = -b₂ (-n)
      rw [show -(n + L) = -n - L by omega, hp.sub_eq]
    · have hL : (1 : ℤ) < L := by
        dsimp [L]
        omega
      have h1 : (1 : ℤ) % L ≠ 0 := by
        rw [Int.emod_eq_of_lt (by decide) hL]
        decide
      exact (hneg 1 h1).trans hone
    · intro n hn
      change -b₂ (-n) = -(-b₂ (-(L - n)))
      rw [hneg n hn, neg_neg, show -(L - n) = n - L by omega, hp.sub_eq]
    · intro n
      -- The reflected indices shift the doubled center by two periods.
      have hs' : ((l - s : ℕ) : ℤ) = (l : ℤ) - s := Nat.cast_sub hs
      have h := hreflect (L + n)
      have hleft : ((l - s : ℕ) : ℤ) - (L + n) = -((s : ℤ) + 1 + n) := by
        dsimp [L]
        omega
      have hright : ((l - s : ℕ) : ℤ) + 1 + (L + n) = -((s : ℤ) - n) + L + L := by
        dsimp [L]
        omega
      rw [hleft, hright, hp, hp] at h
      exact congrArg Neg.neg h.symm
  have hbc : b₁ = c := (existsUnique_gobelBSequence l s hleven hs hcoprime).unique hb₁ hc
  subst b₁
  intro n
  refine ⟨hneg n, fun hn => ?_⟩
  obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr hn
  change -b₂ (-n) = -b₂ n
  rw [hk, mul_comm L k]
  have hpk := hp.int_mul k
  exact congrArg Neg.neg (hpk.neg_eq.trans hpk.eq.symm)

-- The bounds and coprimality are retained from the source statement.
set_option linter.unusedVariables false in
/-- **Translation and reflection identities for $b_{l,s}$.** Let $l \ge 2$ be an even natural
number and $s \le l$ a natural number such that $2s + 1$ and $l + 1$ are coprime, let
$b : \mathbb{Z} \to \mathbb{Z}$ satisfy the defining conditions of $b_{l,s}$, and write
$t = l/2 - s$. Then the following hold. (a) For every integer $n$ such that neither $n$ nor
$n + 2s + 1$ is divisible by $l + 1$, $b(n) = -b(n + 2s + 1)$. (b) If $s < l/2$, then for every
integer $n$ such that neither $n$ nor $n + 2t$ is divisible by $l + 1$, $b(n) = -b(n + 2t)$.
(c) If $s < l/2$, then for every integer $n$ such that neither $t - n$ nor $t + n$ is divisible
by $l + 1$, $b(t - n) = b(t + n)$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 23. -/
public theorem gobelBSequence_translation_identities
    (l s : ℕ) (hleven : Even l) (hs : s ≤ l) (hl2 : 2 ≤ l)
    (hcoprime : Nat.Coprime (2 * s + 1) (l + 1))
    (b : ℤ → ℤ) (hb : IsGobelBSequence l s b) :
    (∀ n : ℤ, Int.emod n (l + 1 : ℤ) ≠ 0 →
      Int.emod (n + (2 * s + 1 : ℕ)) (l + 1 : ℤ) ≠ 0 →
      b n = -b (n + (2 * s + 1 : ℕ))) ∧
    (s < l / 2 →
      ∀ n : ℤ, Int.emod n (l + 1 : ℤ) ≠ 0 →
        Int.emod (n + (2 * (l / 2 - s) : ℕ)) (l + 1 : ℤ) ≠ 0 →
        b n = -b (n + (2 * (l / 2 - s) : ℕ))) ∧
    (s < l / 2 →
      ∀ n : ℤ, Int.emod (((l / 2 - s : ℕ) : ℤ) - n) (l + 1 : ℤ) ≠ 0 →
        Int.emod (((l / 2 - s : ℕ) : ℤ) + n) (l + 1 : ℤ) ≠ 0 →
        b (((l / 2 - s : ℕ) : ℤ) - n) = b (((l / 2 - s : ℕ) : ℤ) + n)) := by
  obtain ⟨_, hperiod, _, hneg, hreflect⟩ := isGobelBSequence_iff.mp hb
  have hshift (n : ℤ) (hn : n % (l + 1 : ℤ) ≠ 0) :
      b n = -b (n + (2 * s + 1 : ℕ)) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hreflect]
    exact hneg n (Int.dvd_iff_emod_eq_zero.not.mpr hn)
  have hshift' (hst : s < l / 2) (n : ℤ)
      (hn : (n + (2 * (l / 2 - s) : ℕ)) % (l + 1 : ℤ) ≠ 0) :
      b n = -b (n + (2 * (l / 2 - s) : ℕ)) := by
    -- The two shifts add to one period.
    have hcomp : 2 * (l / 2 - s) + (2 * s + 1) = l + 1 := by
      obtain ⟨k, hk⟩ := hleven
      omega
    have h := hshift _ hn
    rw [add_assoc, ← Nat.cast_add, hcomp, Nat.cast_add, Nat.cast_one, hperiod] at h
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  refine ⟨fun n hn _ => hshift n hn, fun hst n _ hn => hshift' hst n hn, ?_⟩
  intro hst n hsub hadd
  let t : ℤ := ((l / 2 - s : ℕ) : ℤ)
  have harg : n - t + (2 * (l / 2 - s) : ℕ) = t + n := by dsimp [t]; omega
  have h := hshift' hst (n - t) (by rwa [harg])
  rw [harg] at h
  calc
    b (t - n) = -b (n - t) := by
      simpa only [neg_sub] using hneg (t - n) (Int.dvd_iff_emod_eq_zero.not.mpr hsub)
    _ = b (t + n) := by rw [h, neg_neg]

end MetaMathlibExt
