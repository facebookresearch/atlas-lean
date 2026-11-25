/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Order.MinMax
import MathlibExt.Data.Nat.DyadicBlock

/-! # The NS property and indicator functions of upper intervals -/

namespace MetaMathlibExt

@[expose] public section

/-- **NS property.** A function $h : \mathbb{N} \to \mathbb{N}$ has the *NS property* if it is
monotone (weakly increasing) and, for all $z, z' \in \mathbb{N}$ and every natural number
$i \ge 1$, $\lfloor z / 2^i \rfloor = \lfloor z' / 2^i \rfloor$ implies
$\lfloor h(z) / 2^{i-1} \rfloor = \lfloor h(z') / 2^{i-1} \rfloor$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 11 (text of arXiv:2207.09134v1, NS property in Section 2). -/
public def HasNSProperty (h : ℕ → ℕ) : Prop :=
  Monotone h ∧ ∀ z z' i : ℕ, 0 < i → z / 2 ^ i = z' / 2 ^ i →
    h z / 2 ^ (i - 1) = h z' / 2 ^ (i - 1)

/-- **Constant functions have the NS property.** For every natural number $c$, the constant
function $\mathbb{N} \to \mathbb{N}$ with value $c$ has the NS property.

Source: characteristic lemma for the NS property of Miyadera, Manabe and Singh,
INTEGERS 25 (2025), Article G3, Definition 11. -/
public theorem hasNSProperty_const (c : ℕ) : HasNSProperty fun _ ↦ c :=
  ⟨monotone_const, fun _ _ _ _ _ ↦ rfl⟩

/-- **Constant extension preserves the NS property.** Let $z \in \mathbb{N}$ and let
$h : \mathbb{N} \to \mathbb{N}$ satisfy $h(a) \le h(b)$ whenever $a \le b \le z$, and
$\lfloor h(a) / 2^{i-1} \rfloor = \lfloor h(b) / 2^{i-1} \rfloor$ whenever $a, b \le z$,
$i \ge 1$ and $\lfloor a / 2^i \rfloor = \lfloor b / 2^i \rfloor$. Then the function sending
$x$ to $h(x)$ for $x \le z$ and to $h(z)$ for $x > z$ has the NS property.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 1 (`integers-2025-G3-lem-1`). -/
public theorem hasNSProperty_extend_const (z : ℕ) (h : ℕ → ℕ)
    (hmono : ∀ a b, a ≤ b → b ≤ z → h a ≤ h b)
    (hns : ∀ a b i : ℕ, a ≤ z → b ≤ z → 0 < i → a / 2 ^ i = b / 2 ^ i →
      h a / 2 ^ (i - 1) = h b / 2 ^ (i - 1)) :
    HasNSProperty fun x ↦ if x ≤ z then h x else h z := by
  suffices HasNSProperty (fun x ↦ h (min x z)) by
    simpa only [min_def, apply_ite] using this
  constructor
  · intro a b hab
    exact hmono _ _ (min_le_min_right z hab) (min_le_right b z)
  · intro a b i hi hab
    exact hns _ _ i (min_le_right a z) (min_le_right b z) hi
      (min_div_two_pow_eq_of_div_two_pow_eq hab z)

/-- **The identity function lacks the NS property.** The identity function on the natural
numbers does not have the NS property: $\lfloor 0/2 \rfloor = \lfloor 1/2 \rfloor$, but
$0 \ne 1$.

Source: characteristic lemma for the NS property of Miyadera, Manabe and Singh,
INTEGERS 25 (2025), Article G3, Definition 11. -/
public theorem not_hasNSProperty_id : ¬ HasNSProperty id := fun h ↦ by
  have := h.2 0 1 1 Nat.one_pos rfl
  simp at this

/-- **Halving functions have the NS property.** For every natural number $m \ge 1$, the function
$x \mapsto \lfloor x / 2^m \rfloor$ on $\mathbb{N}$ has the NS property.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 7 (`integers-2025-G3-lem-7`). -/
public theorem hasNSProperty_div_two_pow {m : ℕ} (hm : 0 < m) :
    HasNSProperty fun x ↦ x / 2 ^ m := by
  refine ⟨fun _ _ hab ↦ Nat.div_le_div_right hab, fun z z' i hi h ↦ ?_⟩
  have he : m + (i - 1) = i + (m - 1) := by omega
  simpa only [Nat.div_div_eq_div_mul, ← Nat.pow_add, he] using
    congrArg (fun q : ℕ ↦ q / 2 ^ (m - 1)) h

/-- **Indicator functions with the NS property.** Let $f : \mathbb{N} \to \mathbb{N}$ be monotone,
with $f(x) \le 1$ for all $x$ and $f(x) = 1$ for some $x$. Then $f$ has the NS property if and
only if there is an even $m \in \mathbb{N}$ such that $f$ is the indicator function of
$\{n \in \mathbb{N} : n \ge m\}$, that is, $f(n) = 1$ for $n \ge m$ and $f(n) = 0$ for $n < m$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 9 (`integers-2025-G3-lem-9`). -/
public theorem indicator_Ici_even_iff_hasNSProperty {f : ℕ → ℕ} (hf : Monotone f)
    (hle : ∀ x, f x ≤ 1) (hone : ∃ x, f x = 1) :
    (∃ m, Even m ∧ f = (Set.Ici m).indicator 1) ↔ HasNSProperty f := by
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hstep⟩
    refine ⟨hf, fun z z' i hi hz ↦ ?_⟩
    by_cases hi₁ : i = 1
    · subst i
      change z / 2 = z' / 2 at hz
      have hcut : k + k ≤ z ↔ k + k ≤ z' := by omega
      simp [hstep, Set.indicator, hcut]
    · have hpow : 1 < (2 : ℕ) ^ (i - 1) := Nat.one_lt_pow (by omega) (by decide)
      rw [Nat.div_eq_of_lt ((hle z).trans_lt hpow), Nat.div_eq_of_lt ((hle z').trans_lt hpow)]
  · intro hns
    let m := Nat.find hone
    have hm : f m = 1 := Nat.find_spec hone
    refine ⟨m, ⟨m / 2, ?_⟩, ?_⟩
    · -- Rounding the first input attaining one down to an even number preserves its value.
      have hpair := hns.2 (m / 2 * 2) m 1 (by decide) (by simp)
      have hmin : m ≤ m / 2 * 2 := Nat.find_min' hone (by simpa [hm] using hpair)
      omega
    · funext z
      simp only [Set.indicator, Set.mem_Ici, Pi.one_apply]
      split_ifs with hz
      · exact le_antisymm (hle z) (hm ▸ hf hz)
      · have hne := Nat.find_min hone (show z < m by omega)
        have := hle z
        omega

end

end MetaMathlibExt
