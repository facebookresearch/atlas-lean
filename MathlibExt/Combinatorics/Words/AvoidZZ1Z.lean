/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Words avoiding the consecutive pattern `z, z + 1, z` -/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.OeisConjecturesWanted

@[expose] public section

/-- **Words avoiding the consecutive pattern $z, z+1, z$.** For natural numbers $k$ and $n$,
$f_k(n)$ is the number of words $w_0 w_1 \cdots w_{n-1}$ of length $n$ over the alphabet
$\{0, 1, \dots, k-1\}$ with no position $i$ such that $i + 2 < n$, $w_{i+1} = w_i + 1$ and
$w_{i+2} = w_i$. -/
def avoidZZ1Z (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin k)).filter (fun w =>
    ∀ i : Fin n, ∀ h1 : (i : ℕ) + 1 < n,
      ∀ h2 : (i : ℕ) + 2 < n,
        ¬ (w ⟨(i : ℕ) + 2, h2⟩ = w i ∧
          (w ⟨(i : ℕ) + 1, h1⟩ : ℕ) = (w i : ℕ) + 1))).card

end

private abbrev Avoids {k n : ℕ} (w : Fin n → Fin k) : Prop :=
  ∀ i : Fin n, ∀ h1 : (i : ℕ) + 1 < n,
    ∀ h2 : (i : ℕ) + 2 < n,
      ¬ (w ⟨(i : ℕ) + 2, h2⟩ = w i ∧
        (w ⟨(i : ℕ) + 1, h1⟩ : ℕ) = (w i : ℕ) + 1)

private abbrev GoodWord (k n : ℕ) := {w : Fin n → Fin k // Avoids w}

private theorem card_goodWord (k n : ℕ) : Fintype.card (GoodWord k n) = avoidZZ1Z k n := by
  exact Fintype.card_subtype (fun w => Avoids w)

private theorem avoids_short {k n : ℕ} (w : Fin n → Fin k) (h : n ≤ 2) : Avoids w := by
  intro i h1 h2
  omega

private theorem avoids_tail {k n : ℕ} {v : Fin (n + 1) → Fin k} (h : Avoids v) :
    Avoids (Fin.tail v) := by
  intro i h1 h2 hbad
  have h1' : (i.succ : ℕ) + 1 < n + 1 := by simp only [Fin.val_succ]; omega
  have h2' : (i.succ : ℕ) + 2 < n + 1 := by simp only [Fin.val_succ]; omega
  exact h i.succ h1' h2' hbad

private theorem avoids_cons_iff {k n : ℕ} (x : Fin k) (w : Fin (n + 2) → Fin k) :
    Avoids (Fin.cons x w) ↔ Avoids w ∧ ¬ (w 1 = x ∧ (w 0 : ℕ) = (x : ℕ) + 1) := by
  let v : Fin (n + 3) → Fin k := Fin.cons x w
  change Avoids v ↔ _
  constructor
  · intro h
    refine ⟨by simpa only [v, Fin.tail_cons] using avoids_tail h, ?_⟩
    have h₀ := h 0 (by simp) (by simp)
    change ¬ (v (Fin.succ (1 : Fin (n + 2))) = v 0 ∧
      (v (Fin.succ (0 : Fin (n + 2))) : ℕ) = (v 0 : ℕ) + 1) at h₀
    simpa only [v, Fin.cons_zero, Fin.cons_succ] using h₀
  · rintro ⟨hw, hstart⟩ i
    refine Fin.cases ?_ ?_ i
    · intro h1 h2 hb
      change v (Fin.succ (1 : Fin (n + 2))) = v 0 ∧
        (v (Fin.succ (0 : Fin (n + 2))) : ℕ) = (v 0 : ℕ) + 1 at hb
      exact hstart (by simpa only [v, Fin.cons_zero, Fin.cons_succ] using hb)
    · intro j h1 h2 hb
      simp only [Fin.val_succ] at h1 h2
      have h1' : (j : ℕ) + 1 < n + 2 := by omega
      have h2' : (j : ℕ) + 2 < n + 2 := by omega
      change v (Fin.succ ⟨(j : ℕ) + 2, h2'⟩) = v j.succ ∧
        (v (Fin.succ ⟨(j : ℕ) + 1, h1'⟩) : ℕ) = (v j.succ : ℕ) + 1 at hb
      exact hw j h1' h2' (by simpa only [v, Fin.cons_succ] using hb)

private theorem avoids_cons_of_le_first {k n : ℕ} (x : Fin k) (w : Fin (n + 1) → Fin k)
    (hw : Avoids w) (hx : (w 0 : ℕ) ≤ x) : Avoids (Fin.cons x w) := by
  cases n with
  | zero => exact avoids_short _ (by decide)
  | succ n => exact (avoids_cons_iff x w).mpr ⟨hw, fun h => by omega⟩

private abbrev Extension (k n : ℕ) := Fin k × GoodWord k (n + 2)

private abbrev BadStart {k n : ℕ} (p : Extension k n) : Prop :=
  p.2.1 1 = p.1 ∧ (p.2.1 0 : ℕ) = (p.1 : ℕ) + 1

private abbrev Advanceable (k n : ℕ) :=
  {w : GoodWord k (n + 1) // (w.1 0 : ℕ) + 1 < k}

-- A good word of length at least three is a good tail with a legal first letter.
private def goodExtensionEquiv (k n : ℕ) :
    GoodWord k (n + 3) ≃ {p : Extension k n // ¬ BadStart p} where
  toFun w := by
    let p : Extension k n := (w.1 0, ⟨Fin.tail w.1, avoids_tail w.2⟩)
    refine ⟨p, (avoids_cons_iff p.1 p.2.1).mp ?_ |>.2⟩
    simpa only [p, Fin.cons_self_tail] using w.2
  invFun p := ⟨Fin.cons p.1.1 p.1.2.1, (avoids_cons_iff _ _).mpr ⟨p.1.2.2, p.2⟩⟩
  left_inv w := Subtype.ext (Fin.cons_self_tail w.1)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (Fin.cons p.1.1 p.1.2.1 : Fin (n + 3) → Fin k) 0 = p.1.1
      exact Fin.cons_zero _ _
    · apply Subtype.ext
      change Fin.tail (Fin.cons p.1.1 p.1.2.1 : Fin (n + 3) → Fin k) = p.1.2.1
      exact Fin.tail_cons _ _

-- The bad extension `x, x+1, x, …` is determined by its good suffix `x, …`,
-- whose first letter has a successor in the alphabet.
private def badExtensionEquiv (k n : ℕ) :
    {p : Extension k n // BadStart p} ≃ Advanceable k n where
  toFun p := by
    refine ⟨⟨Fin.tail p.1.2.1, avoids_tail p.1.2.2⟩, ?_⟩
    change (p.1.2.1 1 : ℕ) + 1 < k
    rw [p.2.1, ← p.2.2]
    exact (p.1.2.1 0).isLt
  invFun w := by
    let x := w.1.1 0
    let y : Fin k := ⟨(x : ℕ) + 1, w.2⟩
    let v : Fin (n + 2) → Fin k := Fin.cons y w.1.1
    refine ⟨(x, ⟨v, avoids_cons_of_le_first y _ w.1.2 (Nat.le_succ _)⟩), ?_⟩
    change v (Fin.succ (0 : Fin (n + 1))) = x ∧ (v 0 : ℕ) = (x : ℕ) + 1
    simp only [v, Fin.cons_succ, Fin.cons_zero, x, y, and_self]
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.1
    · apply Subtype.ext
      have h : (Fin.tail p.1.2.1 0 : ℕ) + 1 = (p.1.2.1 0 : ℕ) := by
        change (p.1.2.1 1 : ℕ) + 1 = _
        rw [p.2.1]
        exact p.2.2.symm
      have hlt : (Fin.tail p.1.2.1 0 : ℕ) + 1 < k := by
        rw [h]
        exact (p.1.2.1 0).isLt
      let y : Fin k := ⟨(Fin.tail p.1.2.1 0 : ℕ) + 1, hlt⟩
      have hy : y = p.1.2.1 0 := Fin.ext h
      change (Fin.cons y (Fin.tail p.1.2.1) : Fin (n + 2) → Fin k) = p.1.2.1
      rw [hy, Fin.cons_self_tail]
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    let y : Fin k := ⟨(w.1.1 0 : ℕ) + 1, w.2⟩
    change Fin.tail (Fin.cons y w.1.1 : Fin (n + 2) → Fin k) = w.1.1
    exact Fin.tail_cons _ _

-- The largest letter can always be prepended without introducing a forbidden triple.
private def maxStartEquiv (k n : ℕ) (hk : 1 ≤ k) :
    {w : GoodWord k (n + 1) // ¬ ((w.1 0 : ℕ) + 1 < k)} ≃ GoodWord k n := by
  let top : Fin k := ⟨k - 1, by omega⟩
  have htop (w : Fin n → Fin k) (hw : Avoids w) : Avoids (Fin.cons top w) := by
    cases n with
    | zero => exact avoids_short _ (by decide)
    | succ n =>
      apply avoids_cons_of_le_first top w hw
      have h := (w 0).isLt
      change (w 0 : ℕ) ≤ k - 1
      omega
  refine
    { toFun := fun w => ⟨Fin.tail w.1.1, avoids_tail w.1.2⟩
      invFun := fun w => ⟨⟨Fin.cons top w.1, htop w.1 w.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · let v : Fin (n + 1) → Fin k := Fin.cons top w.1
    change ¬ ((v 0 : ℕ) + 1 < k)
    simp only [v, Fin.cons_zero]
    change ¬ (k - 1 + 1 < k)
    omega
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    have ht : top = w.1.1 0 := by
      apply Fin.ext
      have hp := w.2
      have hb := (w.1.1 0).isLt
      change k - 1 = (w.1.1 0 : ℕ)
      omega
    change Fin.cons top (Fin.tail w.1.1) = w.1.1
    rw [ht, Fin.cons_self_tail]
  · intro w
    apply Subtype.ext
    change Fin.tail (Fin.cons top w.1 : Fin (n + 1) → Fin k) = w.1
    exact Fin.tail_cons _ _

private theorem avoidZZ1Z_short (k n : ℕ) (hn : n ≤ 2) : avoidZZ1Z k n = k ^ n := by
  let e : GoodWord k n ≃ (Fin n → Fin k) :=
    { toFun := Subtype.val
      invFun := fun w => ⟨w, avoids_short w hn⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  calc
    avoidZZ1Z k n = Fintype.card (GoodWord k n) := (card_goodWord k n).symm
    _ = Fintype.card (Fin n → Fin k) := Fintype.card_congr e
    _ = k ^ n := by simp

private theorem avoidZZ1Z_step (k n : ℕ) (hk : 1 ≤ k) :
    (avoidZZ1Z k (n + 3) : ℤ) = k * avoidZZ1Z k (n + 2) -
      avoidZZ1Z k (n + 1) + avoidZZ1Z k n := by
  have hbad := Fintype.card_congr (badExtensionEquiv k n)
  have hgood := Fintype.card_congr (goodExtensionEquiv k n)
  rw [card_goodWord, Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_fin,
    card_goodWord, hbad] at hgood
  have hmax := Fintype.card_congr (maxStartEquiv k n hk)
  rw [Fintype.card_subtype_compl, card_goodWord, card_goodWord] at hmax
  change avoidZZ1Z k (n + 1) - Fintype.card (Advanceable k n) = avoidZZ1Z k n at hmax
  have hb : Fintype.card (Advanceable k n) ≤ k * avoidZZ1Z k (n + 2) := by
    simpa only [hbad, Fintype.card_prod, Fintype.card_fin, card_goodWord] using
      Fintype.card_subtype_le (fun p : Extension k n => BadStart p)
  have ha : Fintype.card (Advanceable k n) ≤ avoidZZ1Z k (n + 1) := by
    simpa only [card_goodWord] using
      Fintype.card_subtype_le (fun w : GoodWord k (n + 1) => (w.1 0 : ℕ) + 1 < k)
  have hnat : avoidZZ1Z k (n + 3) + avoidZZ1Z k (n + 1) =
      k * avoidZZ1Z k (n + 2) + avoidZZ1Z k n := by omega
  have hint : (avoidZZ1Z k (n + 3) : ℤ) + avoidZZ1Z k (n + 1) =
      k * avoidZZ1Z k (n + 2) + avoidZZ1Z k n := by exact_mod_cast hnat
  omega

/-- **Recurrence for words avoiding the pattern $z, z+1, z$.** Let $k \ge 1$ and, for each
natural number $n$, let $f_k(n)$ be the number of words of length $n$ over the alphabet
$\{0, 1, \dots, k-1\}$ that avoid the consecutive pattern $z, z+1, z$. Then $f_k(0) = 1$,
$f_k(1) = k$, $f_k(2) = k^2$, and $f_k(n) = k f_k(n-1) - f_k(n-2) + f_k(n-3)$ for every $n \ge 3$.

At $k = 0$ the recurrence would read $0 = 1$ at $n = 3$.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 3. -/
public theorem avoidZZ1Z_spec (k : ℕ) (hk : 1 ≤ k) :
    avoidZZ1Z k 0 = 1 ∧ avoidZZ1Z k 1 = k ∧
      avoidZZ1Z k 2 = k ^ 2 ∧
      ∀ n : ℕ, 3 ≤ n →
        (avoidZZ1Z k n : ℤ) =
          (k : ℤ) * avoidZZ1Z k (n - 1) -
            avoidZZ1Z k (n - 2) + avoidZZ1Z k (n - 3) := by
  refine ⟨by simpa using avoidZZ1Z_short k 0 (by decide),
    by simpa using avoidZZ1Z_short k 1 (by decide), avoidZZ1Z_short k 2 le_rfl, ?_⟩
  intro n hn
  have h := avoidZZ1Z_step k (n - 3) hk
  rw [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
    show n - 3 + 1 = n - 2 by omega] at h
  exact h

end MathlibExt.NumberTheory.OeisConjecturesWanted
