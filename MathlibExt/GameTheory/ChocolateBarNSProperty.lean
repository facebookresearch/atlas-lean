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
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Order.MinMax
import MathlibExt.Data.Nat.DyadicBlock

/-! # The NS property of chocolate-bar games

This module characterizes upper-interval indicators with the NS property and proves
that clamping coordinates by NS functions preserves the set of nim-sums below a given width.
-/

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

/-- **Quotients of a truncated NS function by powers of two.** Let $h : \mathbb{N} \to \mathbb{N}$
have the NS property and let $z, z', k \in \mathbb{N}$ with $k \ge 1$ and
$\lfloor z' / 2^k \rfloor = \lfloor z / 2^k \rfloor$. Then for every $y \in \mathbb{N}$,
$\lfloor \min(h(z'), y) / 2^{k-1} \rfloor = \lfloor \min(h(z), y) / 2^{k-1} \rfloor$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 2 (ii) (`integers-2025-G3-lem-2`). -/
public theorem HasNSProperty.min_div_two_pow_eq {h : ℕ → ℕ} (hh : HasNSProperty h)
    {z z' k : ℕ} (hk : 0 < k) (hz : z' / 2 ^ k = z / 2 ^ k) (y : ℕ) :
    min (h z') y / 2 ^ (k - 1) = min (h z) y / 2 ^ (k - 1) :=
  min_div_two_pow_eq_of_div_two_pow_eq (hh.2 z' z k hk hz) y

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

namespace image_foldl_xor_eq_image_min

-- At the highest bit where a and b differ, the masks agree from that bit upwards.
private theorem xor_lt_of_dyadic_agreement {g : ℕ → ℕ}
    (hg : ∀ a b k, a / 2 ^ (k + 1) = b / 2 ^ (k + 1) → g a / 2 ^ k = g b / 2 ^ k)
    {a b : ℕ} (hab : a < b) : g b ^^^ (g a ^^^ a) < b := by
  obtain ⟨k, hne, heq⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun k ↦ a / 2 ^ k = b / 2 ^ k) (by simpa using hab.ne)
    ⟨b, by rw [Nat.div_eq_of_lt (hab.trans Nat.lt_two_pow_self),
      Nat.div_eq_of_lt Nat.lt_two_pow_self]⟩
  apply Nat.lt_of_div_lt_div (c := 2 ^ k)
  simpa only [Nat.xor_div_two_pow, hg a b k heq, Nat.xor_xor_cancel_left] using
    (Nat.lt_of_le_of_ne (Nat.div_le_div_right hab.le) hne)

end image_foldl_xor_eq_image_min

/-- **Nim-sum sets under clamping by functions with the NS property.** Let $m \in \mathbb{N}$,
let $f_0, \dots, f_{m-1} : \mathbb{N} \to \mathbb{N}$ have the NS property, and let
$x_0, \dots, x_{m-1}, z \in \mathbb{N}$ satisfy $x_t \le f_t(z)$ for every $t < m$. Then
$$
\{x_0 \oplus \cdots \oplus x_{m-1} \oplus w : w < z\} =
\{\min(x_0, f_0(w)) \oplus \cdots \oplus \min(x_{m-1}, f_{m-1}(w)) \oplus w : w < z\},
$$
where $\oplus$ denotes nim-sum (bitwise exclusive or).

The printed left-hand nim-sum carries a stray index $j \ne i$ with $i$ unbound; it is read as the
full nim-sum, as in Lemma 5 (the case of two functions), which the proof generalises.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 6 (`integers-2025-G3-lem-6`). -/
public theorem image_foldl_xor_eq_image_min {m : ℕ} {f : Fin m → ℕ → ℕ}
    (hf : ∀ t, HasNSProperty (f t)) {x : Fin m → ℕ} {z : ℕ} (hx : ∀ t, x t ≤ f t z) :
    {c | ∃ w < z, c = (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ w} =
      {c | ∃ w < z, c = (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0 ^^^ w} := by
  let g (w : ℕ) := (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0
  have gz : g z = (List.ofFn x).foldl (· ^^^ ·) 0 := by simp [g, min_eq_left (hx _)]
  have hlt {a b : ℕ} (hab : a < b) : g b ^^^ (g a ^^^ a) < b := by
    refine image_foldl_xor_eq_image_min.xor_lt_of_dyadic_agreement ?_ hab
    intro u v k huv
    have hdiv (l : List ℕ) : l.foldl (· ^^^ ·) 0 / 2 ^ k =
        (l.map (· / 2 ^ k)).foldl (· ^^^ ·) 0 := by
      simpa only [Nat.zero_div] using
        (List.foldl_map_hom (l := l) (a := 0) (g := (· / 2 ^ k))
          (f := (· ^^^ ·)) (f' := (· ^^^ ·)) fun _ _ ↦ Nat.xor_div_two_pow.symm).symm
    simp only [g, hdiv, List.map_ofFn]
    congr 2
    funext t
    have ht := (hf t).2 u v (k + 1) (Nat.zero_lt_succ _) huv
    simpa [Function.comp_def, min_comm (x t)] using
      min_div_two_pow_eq_of_div_two_pow_eq (k := k) (by simpa using ht) (x t)
  -- Removing the mask at z sends each clamped nim-sum to a width below z.
  let perm (w : Fin z) : Fin z := ⟨g z ^^^ (g w ^^^ w), hlt w.isLt⟩
  have hinj : Function.Injective perm := by
    intro u v h
    have he : g u ^^^ u.val = g v ^^^ v.val := Nat.xor_right_injective (congrArg Fin.val h)
    apply Fin.ext
    rcases lt_trichotomy u.val v.val with huv | huv | hvu
    · simpa [he] using hlt huv
    · exact huv
    · simpa [← he] using hlt hvu
  rw [← gz]
  ext c
  change (∃ w < z, c = g z ^^^ w) ↔ ∃ w < z, c = g w ^^^ w
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj (⟨w, hw⟩ : Fin z)
    exact ⟨v, v.isLt, by simpa [perm] using congrArg (fun i : Fin z ↦ g z ^^^ i.val) hv.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨perm ⟨w, hw⟩, (perm ⟨w, hw⟩).isLt, by simp [perm]⟩

end

end MetaMathlibExt
