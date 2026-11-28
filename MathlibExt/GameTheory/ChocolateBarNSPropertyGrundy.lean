/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Nat.Bitwise
import MathlibExt.Data.Nat.DyadicBlock
import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtXorXor
import MathlibExt.GameTheory.ChocolateBarNSPropertyImageXorXorEq

/-! # Grundy numbers of chocolate bars with two shape functions

For monotone shape functions `g` and `h`, both functions have the NS property exactly when the
Grundy number is `x ^^^ y ^^^ z` at every legal bar, with `x ≤ g z` and `y ≤ h z`.
Taking `g = f` for a monotone shape function `f` and `h` constantly zero forces `y = 0`:
`f` has the NS property exactly when the Grundy number is `x ^^^ z` for every `x ≤ f z`.
As in the proof of Theorem 4, the height and depth bounds are the bounds at width `z`;
this is the legal-coordinate convention for Theorem 2.

## References

* Ryohei Miyadera, Hikaru Manabe and Aditi Singh,
  *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*,
  INTEGERS 25 (2025), Article G3, pp. 1–29, Definitions 2 and 8–11, Lemmas 3 and 5,
  and Theorems 2 and 4.
* Ryohei Miyadera, Shunsuke Nakamura and Yushi Nakaya,
  *Grundy Numbers of Impartial Chocolate Bar Games*, INTEGERS 20 (2020), Article G1,
  pp. 1–30, Definition 1.2 and Theorems 4 and 5 (the original one-function result cited by
  Theorem 2); also Lemmas 10 and 11 (for the one-coordinate converse).
* The Lean proof uses `HasNSProperty.exists_of_lt_xor_xor` from
  `MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtXorXor`,
  `HasNSProperty.image_xor_xor_eq` from `MathlibExt.GameTheory.ChocolateBarNSPropertyImageXorXorEq`,
  and the dyadic block lemmas from `MathlibExt.Data.Nat.DyadicBlock`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Grundy number of a chocolate bar.** Let $f_1, \dots, f_s : \mathbb{N} \to \mathbb{N}$. For
coordinates $x = (x_1, \dots, x_s) \in \mathbb{N}^s$ and a width $z \in \mathbb{N}$, the position
$(x, z)$ stands for the chocolate bar $\mathrm{CB}(f_1, \dots, f_s, x_1, \dots, x_s, z)$, whose
column at width $w \le z$ extends $\min(f_t(w), x_t) + 1$ cells along axis $t$. A move either
lowers one coordinate $x_i$ to some $u < x_i$, keeping the width $z$, or cuts the width to some
$w < z$, which replaces every $x_t$ by $\min(x_t, f_t(w))$. The Grundy number of $(x, z)$ is the
mex (least natural number not attained) of the Grundy numbers of the positions reachable from
$(x, z)$ in one move. It is defined for all $(x, z)$; the bars themselves are the positions with
$x_t \le f_t(z)$ for all $t$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 2, 8, 9 and 10 (two functions) and Section 4, before Theorem 5
(four functions). -/
public noncomputable def chocolateBarGrundy {s : ℕ} (f : Fin s → ℕ → ℕ) (x : Fin s → ℕ)
    (z : ℕ) : ℕ :=
  sInf {m | (∀ i u, u < x i → chocolateBarGrundy f (Function.update x i u) z ≠ m) ∧
    ∀ w, w < z → chocolateBarGrundy f (fun t ↦ min (x t) (f t w)) w ≠ m}
termination_by z + ∑ t, x t
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hj]
    omega
  · have hle : ∑ t, min (x t) (f t w) ≤ ∑ t, x t :=
      Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
    omega

/-- **Mex recursion for the Grundy number of a chocolate bar.** Let $f_1, \dots, f_s$ be
functions $\mathbb{N} \to \mathbb{N}$ and write $G(x, z)$ for the Grundy number of the chocolate
bar with coordinates $x = (x_1, \dots, x_s) \in \mathbb{N}^s$ and width $z \in \mathbb{N}$. For
all $x$ and $z$, $G(x, z)$ is the least natural number $m$ such that $m \ne G(x', z)$ for every
$x'$ obtained from $x$ by replacing one coordinate $x_i$ with some $u < x_i$, and
$m \ne G(x^{(w)}, w)$ for every $w < z$, where $x^{(w)}_t = \min(x_t, f_t(w))$ for all $t$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 9 and 10. -/
public theorem chocolateBarGrundy_eq {s : ℕ} (f : Fin s → ℕ → ℕ) (x : Fin s → ℕ) (z : ℕ) :
    chocolateBarGrundy f x z =
      sInf {m | (∀ i u, u < x i → chocolateBarGrundy f (Function.update x i u) z ≠ m) ∧
        ∀ w, w < z → chocolateBarGrundy f (fun t ↦ min (x t) (f t w)) w ≠ m} := by
  rw [chocolateBarGrundy]

private theorem chocolateBarGrundy_two_eq (g h : ℕ → ℕ) (x y z : ℕ) :
    chocolateBarGrundy ![g, h] ![x, y] z =
      sInf {m | (∀ u < x, chocolateBarGrundy ![g, h] ![u, y] z ≠ m) ∧
        (∀ v < y, chocolateBarGrundy ![g, h] ![x, v] z ≠ m) ∧
        ∀ w < z, chocolateBarGrundy ![g, h] ![min x (g w), min y (h w)] w ≠ m} := by
  have h₀ (u : ℕ) : Function.update (![x, y] : Fin 2 → ℕ) 0 u = ![u, y] := by
    funext j
    revert j
    rw [Fin.forall_fin_two]
    constructor <;> simp
  have h₁ (v : ℕ) : Function.update (![x, y] : Fin 2 → ℕ) 1 v = ![x, v] := by
    funext j
    revert j
    rw [Fin.forall_fin_two]
    constructor <;> simp
  have hw (w : ℕ) : (fun t ↦ min (![x, y] t) (![g, h] t w)) =
      ![min x (g w), min y (h w)] := by
    funext j
    revert j
    rw [Fin.forall_fin_two]
    constructor <;> rfl
  rw [chocolateBarGrundy_eq]
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    h₀, h₁, hw, and_assoc]

private theorem chocolateBarGrundy_eq_xor {g h : ℕ → ℕ} (hg : HasNSProperty g)
    (hh : HasNSProperty h) (x y z : ℕ) (hx : x ≤ g z) (hy : y ≤ h z) :
    chocolateBarGrundy ![g, h] ![x, y] z = x ^^^ y ^^^ z := by
  have hleft (u : ℕ) (hu : u < x) : chocolateBarGrundy ![g, h] ![u, y] z = u ^^^ y ^^^ z :=
    chocolateBarGrundy_eq_xor hg hh u y z (hu.le.trans hx) hy
  have hright (v : ℕ) (hv : v < y) : chocolateBarGrundy ![g, h] ![x, v] z = x ^^^ v ^^^ z :=
    chocolateBarGrundy_eq_xor hg hh x v z hx (hv.le.trans hy)
  have hcut (w : ℕ) (hw : w < z) : chocolateBarGrundy ![g, h] ![min x (g w), min y (h w)] w =
      min (g w) x ^^^ min (h w) y ^^^ w := by
    rw [chocolateBarGrundy_eq_xor hg hh (min x (g w)) (min y (h w)) w
      (min_le_right ..) (min_le_right ..), min_comm x, min_comm y]
  rw [chocolateBarGrundy_two_eq]
  let missing : Set ℕ := {m | (∀ u < x, chocolateBarGrundy ![g, h] ![u, y] z ≠ m) ∧
    (∀ v < y, chocolateBarGrundy ![g, h] ![x, v] z ≠ m) ∧
    ∀ w < z, chocolateBarGrundy ![g, h] ![min x (g w), min y (h w)] w ≠ m}
  change sInf missing = _
  have hmissing : x ^^^ y ^^^ z ∈ missing := by
    refine ⟨fun u hu he ↦ hu.ne (by simpa using (hleft u hu).symm.trans he),
      fun v hv he ↦ hv.ne (by simpa using (hright v hv).symm.trans he), ?_⟩
    intro w hw he
    have hmem : x ^^^ y ^^^ z ∈ {c | ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w} :=
      ⟨w, hw, he.symm.trans (hcut w hw)⟩
    rw [← HasNSProperty.image_xor_xor_eq hg hh hx hy] at hmem
    obtain ⟨v, hv, heq⟩ := hmem
    exact hv.ne (Nat.xor_right_inj.mp heq).symm
  apply le_antisymm (Nat.sInf_le hmissing)
  by_contra! hlt
  have hm := Nat.sInf_mem ⟨_, hmissing⟩
  rcases HasNSProperty.exists_of_lt_xor_xor hg hh hx hy hlt with
      ⟨u, hu, he⟩ | ⟨v, hv, he⟩ | ⟨w, hw, he⟩
  · exact hm.1 u hu ((hleft u hu).trans he.symm)
  · exact hm.2.1 v hv ((hright v hv).trans he.symm)
  · exact hm.2.2 w hw ((hcut w hw).trans he.symm)
termination_by x + y + z
decreasing_by
  all_goals omega

private theorem hasNSProperty_of_single_mex {f : ℕ → ℕ} {G : ℕ → ℕ → ℕ}
    (hf : Monotone f)
    (hrec : ∀ y z, G y z = sInf {m | (∀ v < y, G v z ≠ m) ∧
      ∀ w < z, G (min y (f w)) w ≠ m})
    (hxor : ∀ y z, y ≤ f z → G y z = y ^^^ z) : HasNSProperty f := by
  have hnoWidth (y z w : ℕ) (hw : w < z) : G (min y (f w)) w ≠ G y z := by
    classical
    let moves := ((Finset.range y).image fun v ↦ G v z) ∪
      ((Finset.range z).image fun w ↦ G (min y (f w)) w)
    obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset moves
    have hgaps : {m | (∀ v < y, G v z ≠ m) ∧ ∀ u < z, G (min y (f u)) u ≠ m}.Nonempty := by
      refine ⟨m, ?_⟩
      constructor
      · intro v hv hEq
        exact hm (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, hEq⟩))
      · intro u hu hEq
        exact hm (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, hEq⟩))
    rw [hrec y z]
    exact (Nat.sInf_mem hgaps).2 w hw
  have hhit (y z m : ℕ) (hm : m < G y z) :
      (∃ v < y, G v z = m) ∨ ∃ w < z, G (min y (f w)) w = m := by
    rw [hrec y z] at hm
    have h := Nat.notMem_of_lt_sInf hm
    simpa only [Set.mem_ofPred_eq, not_and_or, not_forall, not_imp, ne_eq, not_not,
      exists_prop] using h
  -- A sufficiently wide bar forces all small targets of the form y xor w to come from width cuts.
  have hwidth (y z : ℕ) (hy : y ≤ f z) :
      {m | ∃ w < z, G (min y (f w)) w = m} = {m | ∃ w < z, y ^^^ w = m} := by
    ext m
    constructor
    · rintro ⟨w, hw, rfl⟩
      let u := y ^^^ G (min y (f w)) w
      have he : y ^^^ u = G (min y (f w)) w := Nat.xor_xor_cancel_left ..
      refine ⟨u, ?_, he⟩
      by_contra! hu
      exact hnoWidth y u w (hw.trans_le hu) ((hxor y u (hy.trans (hf hu))).trans he).symm
    · rintro ⟨w, hw, rfl⟩
      let k := max y z
      have hyk : y < 2 ^ k := (le_max_left y z).trans_lt Nat.lt_two_pow_self
      have hzk : z < 2 ^ k := (le_max_right y z).trans_lt Nat.lt_two_pow_self
      have hlarge {v : ℕ} (hv : v < 2 ^ k) : 2 ^ k ≤ v ^^^ 2 ^ k := by
        by_contra! hsmall
        exact (Nat.lt_irrefl (2 ^ k)) (by
          simpa only [Nat.xor_xor_cancel_left] using Nat.xor_lt_two_pow hv hsmall)
      have hm : y ^^^ w < G y (2 ^ k) := by
        rw [hxor y _ (hy.trans (hf hzk.le))]
        exact (Nat.xor_lt_two_pow hyk (hw.trans hzk)).trans_le (hlarge hyk)
      rcases hhit y _ _ hm with ⟨v, hv, he⟩ | ⟨u, hu, he⟩
      · rw [hxor v _ (hv.le.trans (hy.trans (hf hzk.le)))] at he
        exact False.elim ((not_lt_of_ge (hlarge (hv.trans hyk)))
          (he ▸ Nat.xor_lt_two_pow hyk (hw.trans hzk)))
      · refine ⟨u, ?_, he⟩
        by_contra! hzu
        have hyu := hy.trans (hf hzu)
        rw [min_eq_left hyu, hxor y u hyu, Nat.xor_right_inj] at he
        exact hw.not_ge (he ▸ hzu)
  -- It suffices to check adjacent widths in each dyadic block.
  have hadj (a j : ℕ) (ha : a / 2 ^ (j + 1) = (a + 1) / 2 ^ (j + 1)) :
      f a / 2 ^ j = f (a + 1) / 2 ^ j := by
    apply le_antisymm (Nat.div_le_div_right (hf (Nat.le_succ a)))
    by_contra! hlt
    obtain ⟨c, i, t, hji, ht, hy, hX⟩ := exists_split_of_div_two_pow_lt hlt
    let z := a + 1
    let y := f a
    let X := c * 2 ^ (i + 1) + 2 ^ i
    let d := y ^^^ X
    have hzi : a / 2 ^ (i + 1) = z / 2 ^ (i + 1) := by
      have hexp : i + 1 = j + 1 + (i - j) := by omega
      simpa only [Function.comp_apply, Nat.div_div_eq_div_mul, ← pow_add, ← hexp] using
        congrArg (fun n : ℕ ↦ n / 2 ^ (i - j)) ha
    have hyX : y < X := by
      change f a < _
      rw [hy]
      exact Nat.add_lt_add_left ht _
    have hyz : y ≤ f z := hf (Nat.le_succ a)
    have heq : {m | ∃ w < z, G (min y (f w)) w = m} =
        {m | ∃ w < z, G (min X (f w)) w = m} := by
      ext m
      have hmin (w : ℕ) (hw : w < z) : min y (f w) = min X (f w) := by
        have hle : f w ≤ y := hf (Nat.le_of_lt_succ hw)
        rw [min_eq_right hle, min_eq_right (hle.trans hyX.le)]
      exact ⟨fun ⟨w, hw, hm⟩ ↦ ⟨w, hw, (hmin w hw) ▸ hm⟩,
        fun ⟨w, hw, hm⟩ ↦ ⟨w, hw, (hmin w hw).symm ▸ hm⟩⟩
    rw [hwidth y z hyz, hwidth X z hX] at heq
    have hinv (w : ℕ) (hw : w < z) : w ^^^ d < z := by
      have hmem : y ^^^ w ∈ {m | ∃ v < z, y ^^^ v = m} := ⟨w, hw, rfl⟩
      rw [heq] at hmem
      obtain ⟨v, hv, hvw⟩ := hmem
      have h : v = w ^^^ d := calc
        v = X ^^^ (X ^^^ v) := (Nat.xor_xor_cancel_left X v).symm
        _ = X ^^^ (y ^^^ w) := by rw [hvw]
        _ = w ^^^ d := by
          change X ^^^ (y ^^^ w) = w ^^^ (y ^^^ X)
          rw [← Nat.xor_assoc, Nat.xor_comm X y, Nat.xor_comm (y ^^^ X) w]
      exact h ▸ hv
    -- After dropping the low i bits, the mask is 1, so it swaps the two halves of a block.
    have hp := Nat.two_pow_pos i
    have hbase (b : ℕ) : b * 2 ^ (i + 1) = (b * 2) * 2 ^ i := by
      rw [pow_succ, mul_comm (2 ^ i) 2, mul_assoc]
    have hdy : y / 2 ^ i = c * 2 := by
      change f a / 2 ^ i = _
      rw [hy, hbase]
      apply Nat.div_eq_of_lt_le (Nat.le_add_right _ _)
      rwa [Nat.add_mul, Nat.one_mul, Nat.add_lt_add_iff_left]
    have hdX : X / 2 ^ i = c * 2 + 1 := calc
      _ = ((c * 2 + 1) * 2 ^ i) / 2 ^ i := by dsimp only [X]; rw [hbase, add_mul, one_mul]
      _ = _ := Nat.mul_div_cancel _ hp
    have hd : d / 2 ^ i = 1 := by
      have hc : Even (c * 2) := ⟨c, by omega⟩
      change (y ^^^ X) / 2 ^ i = 1
      rw [Nat.xor_div_two_pow, hdy, hdX, ← Nat.xor_one_of_even hc, Nat.xor_xor_cancel_left]
    have hcross : ∀ w : ℕ, (w ^^^ d) / 2 ^ i = (w / 2 ^ i) ^^^ 1 := by
      intro w
      rw [Nat.xor_div_two_pow, hd]
    by_cases hz : Even (z / 2 ^ i)
    · let b := z / 2 ^ (i + 1)
      let start := b * 2 ^ (i + 1)
      have hstart : start < z := by
        have hba : start ≤ a := by
          simpa only [start, b, ← hzi] using Nat.div_mul_le_self a (2 ^ (i + 1))
        exact Nat.lt_succ_of_le hba
      have hquot : z / 2 ^ i / 2 = b := by
        change z / 2 ^ i / 2 = z / 2 ^ (i + 1)
        rw [Nat.div_div_eq_div_mul, pow_succ]
      have hsame : start / 2 ^ i = z / 2 ^ i := by
        change b * 2 ^ (i + 1) / 2 ^ i = _
        rw [hbase, Nat.mul_div_cancel _ hp]
        rcases hz with ⟨q, hq⟩
        omega
      have himage := Nat.div_le_div_right (hinv start hstart).le (c := 2 ^ i)
      rw [hcross, hsame, Nat.xor_one_of_even hz] at himage
      omega
    · have ho : Odd (z / 2 ^ i) := Nat.not_even_iff_odd.mp hz
      have hsmall : z ^^^ d < z := by
        by_contra! hn
        have hquot := Nat.div_le_div_right hn (c := 2 ^ i)
        rw [hcross, Nat.xor_one_of_odd ho] at hquot
        rcases ho with ⟨q, hq⟩
        omega
      simpa only [Nat.xor_xor_cancel_right, lt_irrefl] using hinv (z ^^^ d) hsmall
  refine ⟨hf, fun a b i hi hab ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  change f a / 2 ^ j = f b / 2 ^ j
  wlog hle : a ≤ b generalizing a b
  · exact (this b a hab.symm (by omega)).symm
  induction b, hle using Nat.le_induction with
  | base => rfl
  | succ b hab' ih =>
    have h := Nat.div_le_div_right hab' (c := 2 ^ (j + 1))
    have h' : b / 2 ^ (j + 1) ≤ (b + 1) / 2 ^ (j + 1) :=
      Nat.div_le_div_right (Nat.le_succ b)
    change a / 2 ^ (j + 1) = (b + 1) / 2 ^ (j + 1) at hab
    have hb : a / 2 ^ (j + 1) = b / 2 ^ (j + 1) := by omega
    exact (ih hb).trans (hadj b j (hb.symm.trans hab))

/-- **Nim-sum Grundy numbers of chocolate bars with two functions.** Let
$g, h : \mathbb{N} \to \mathbb{N}$ be monotone. Then $g$ and $h$ both have the NS property if and
only if, for all natural numbers $x, y, z$ with $x \le g(z)$ and $y \le h(z)$, the Grundy number
of the chocolate bar $\mathrm{CB}(g, h, x, y, z)$ equals $x \oplus y \oplus z$, where $\oplus$ is
nim-sum (bitwise exclusive or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 4 (`integers-2025-G3-thm-4`). -/
public theorem hasNSProperty_and_iff_chocolateBarGrundy_eq_xor {g h : ℕ → ℕ}
    (hg : Monotone g) (hh : Monotone h) :
    HasNSProperty g ∧ HasNSProperty h ↔
      ∀ x y z, x ≤ g z → y ≤ h z → chocolateBarGrundy ![g, h] ![x, y] z = x ^^^ y ^^^ z := by
  constructor
  · rintro ⟨hng, hnh⟩ x y z hx hy
    exact chocolateBarGrundy_eq_xor hng hnh x y z hx hy
  · intro hxor
    constructor
    · let G (x z : ℕ) := chocolateBarGrundy ![g, h] ![x, 0] z
      refine hasNSProperty_of_single_mex (G := G) hg (fun x z ↦ ?_) (fun x z hx ↦ ?_)
      · unfold G
        rw [chocolateBarGrundy_two_eq]
        simp
      · simpa [G] using hxor x 0 z hx (Nat.zero_le _)
    · let G (y z : ℕ) := chocolateBarGrundy ![g, h] ![0, y] z
      refine hasNSProperty_of_single_mex (G := G) hh (fun y z ↦ ?_) (fun y z hy ↦ ?_)
      · unfold G
        rw [chocolateBarGrundy_two_eq]
        simp
      · simpa [G] using hxor 0 y z (Nat.zero_le _) hy

/-- **The NS property characterises nim-sum Grundy numbers of two-dimensional chocolate bars.**
Let $f : \mathbb{N} \to \mathbb{N}$ be monotone. Then $f$ has the NS property if and only if, for
all $x, z \in \mathbb{N}$ with $x \le f(z)$, the chocolate bar $\mathrm{CB}(f, 0, x, 0, z)$ of
width $z$ (first function $f$, first coordinate $x$, second function constantly $0$, second
coordinate $0$) has Grundy number $x \oplus z$, where $\oplus$ denotes nim-sum (bitwise exclusive
or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 2 (`integers-2025-G3-thm-2`). -/
public theorem hasNSProperty_iff_chocolateBarGrundy_depth_zero {f : ℕ → ℕ}
    (hf : Monotone f) :
    HasNSProperty f ↔
      ∀ x z, x ≤ f z → chocolateBarGrundy ![f, fun _ ↦ 0] ![x, 0] z = x ^^^ z := by
  have htwo := hasNSProperty_and_iff_chocolateBarGrundy_eq_xor (h := fun _ ↦ 0) hf monotone_const
  constructor
  · intro hns x z hx
    simpa only [Nat.xor_zero] using htwo.mp ⟨hns, hasNSProperty_const 0⟩ x 0 z hx le_rfl
  · intro hxor
    refine (htwo.mpr (fun x y z hx hy ↦ ?_)).1
    obtain rfl := Nat.eq_zero_of_le_zero hy
    simpa only [Nat.xor_zero] using hxor x z hx

end

end MetaMathlibExt
