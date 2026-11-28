/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Reflection-fixed tilings of a cylinder

For positive dimensions $n$ and $m$, let $T$ be a finite set of tile designs with decidable
equality and let $\sigma$ be a permutation of $T$ with $\sigma^2=1$. The two formulas count
tilings $F : \mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z} \to T$ satisfying
$F(-1-x-a,y)=\sigma(F(x,y))$ at every cell, summed over the horizontal shifts
$a \in \mathbb{Z}/n\mathbb{Z}$. For `cylinder_f_even` ($n$ even), even shifts leave no fixed
columns and odd shifts leave two, where the parity refers to the least nonnegative
representative of $a$. For `cylinder_f_odd` ($n$ odd), every shift leaves exactly one fixed
column. A reflected pair takes any design, while a fixed cell takes a design fixed by $\sigma$.

## References

* Peter Kagey and William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 20 (p. 12), Lemma 25
  (pp. 16–17), and Theorem 30, Equations (26a) and (26b) (pp. 19–20).
  <https://cs.uwaterloo.ca/journals/JIS/VOL27/Kagey/kagey6.html>
* `MathlibExt.Combinatorics.Enumerative.GridCylinderTorusTilings`: `fixedTilingsEquiv` chooses
  tiles on one representative per pair and on the fixed cells; `reflection_shift_solutions_odd`
  identifies the unique fixed column when the width is odd.
-/

namespace MetaMathlibExt

private theorem card_fixedColumns {n : ℕ} [NeZero n] (hn : Even n) (a : ZMod n) :
    Fintype.card {x : ZMod n // -1 - x - a = x} = if Even a.val then 0 else 2 := by
  classical
  split_ifs with ha
  · have h := reflection_shift_solutions_even_even n a hn ha
    let hEmpty : IsEmpty {x : ZMod n // -1 - x - a = x} :=
      ⟨fun x => (Set.eq_empty_iff_forall_notMem.mp h x) x.property.symm⟩
    exact @Fintype.card_of_isEmpty _ _ hEmpty
  · have ha' := Nat.not_even_iff_odd.mp ha
    let x : ℤ := (-1 - a.val) / 2
    let y : ℤ := ((n : ℤ) - 1 - a.val) / 2
    have hmem (b : ZMod n) : -1 - b - a = b ↔ b = (x : ZMod n) ∨ b = (y : ZMod n) :=
      eq_comm.trans (by simpa only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        using Set.ext_iff.mp (reflection_shift_solutions_even_odd n a hn ha') b)
    obtain ⟨k, hk⟩ := hn
    have hdiff : y - x = (k : ℤ) := by
      dsimp [x, y]
      omega
    have hne : (x : ZMod n) ≠ (y : ZMod n) := by
      intro hxy
      have hz : ((k : ℕ) : ZMod n) = 0 := by
        rw [← Int.cast_natCast, ← hdiff, Int.cast_sub, hxy, sub_self]
      have hdvd := (ZMod.natCast_eq_zero_iff k n).mp hz
      have hn₀ := NeZero.ne n
      have hkn := Nat.le_of_dvd (by omega : 0 < k) hdvd
      omega
    exact (Fintype.card_congr (Equiv.subtypeEquivRight hmem)).trans
      (Fintype.card_subtype_eq_or_eq_of_ne hne)

private theorem fixedTilingCount_shiftedReflection {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (a : ZMod n) (σ : Equiv.Perm T)
    (hσ : Function.Involutive σ) :
    let k := Fintype.card {x : ZMod n // -1 - x - a = x}
    fixedTilingCount (fun c => cellF n m (c.1 + a, c.2)) σ =
      Fintype.card T ^ ((n * m - k * m) / 2) * tileFixedCount σ 1 ^ (k * m) := by
  classical
  intro k
  let C := ZMod n × ZMod m
  let r (x : ZMod n) := -1 - x - a
  let φ (c : C) : C := (r c.1, c.2)
  have hφ : Function.Involutive φ := fun c => Prod.ext (by dsimp [φ, r]; ring) rfl
  let p (c : C) := c.1.val < (φ c).1.val
  let q (c : C) := φ c = c
  let p' (c : C) := (φ c).1.val < c.1.val
  have hfixed (c : C) : q c ↔ r c.1 = c.1 :=
    ⟨congrArg Prod.fst, fun h => Prod.ext h rfl⟩
  have hval (c : C) : r c.1 = c.1 ↔ (φ c).1.val = c.1.val := by
    change r c.1 = c.1 ↔ (r c.1).val = c.1.val
    exact ⟨congrArg ZMod.val, fun h => ZMod.val_injective n h⟩
  have hneq (c : C) : ¬q c ↔ (φ c).1.val ≠ c.1.val :=
    not_congr ((hfixed c).trans (hval c))
  have hflip (c : C) (hc : ¬q c) : p (φ c) ↔ ¬p c := by
    have h := (hneq c).mp hc
    simp only [p, hφ c]
    omega
  have hp (c : C) (hc : q c) : ¬p c := by simp [p, show φ c = c from hc]
  -- The reflection bijects the representatives with the other cells in their pairs.
  have hpair : Fintype.card (Subtype p) = Fintype.card (Subtype p') :=
    Fintype.card_congr ((hφ.toPerm φ).subtypeEquiv fun c => by
      change p c ↔ p' (φ c)
      simp [p, p', hφ c])
  have hnonfixed : Fintype.card {c // ¬q c} = Fintype.card (Subtype p) +
      Fintype.card (Subtype p') := by
    refine (Fintype.card_congr (Equiv.subtypeEquivRight fun c => ?_)).trans
      (Fintype.card_subtype_or_disjoint p p' ?_)
    · exact (hneq c).trans ⟨fun h => (lt_or_gt_of_ne h).symm,
        fun h => h.elim ne_of_gt ne_of_lt⟩
    · exact fun _ h₁ h₂ c hc => (lt_asymm (h₁ c hc) (h₂ c hc)).elim
  have hcard : Fintype.card (Subtype q) = k * m := by
    let e := (Equiv.subtypeEquivRight hfixed).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun x : ZMod n => r x = x))
    rw [Fintype.card_congr e, Fintype.card_prod, ZMod.card]
  have htotal := Fintype.card_subtype_compl q
  rw [hnonfixed, ← hpair, hcard] at htotal
  simp only [C, Fintype.card_prod, ZMod.card] at htotal
  have hrep : Fintype.card (Subtype p) = (n * m - k * m) / 2 := by omega
  have hshift (c : C) : cellF n m (c.1 + a, c.2) = φ c := by
    refine Prod.ext ?_ rfl
    dsimp [cellF, φ, r]
    ring
  simp_rw [hshift]
  calc
    fixedTilingCount φ σ = Fintype.card
        ((Subtype p → T) × (Subtype q → {d : T // σ d = d})) :=
      Fintype.card_congr (fixedTilingsEquiv φ hφ p hp hflip σ hσ)
    _ = _ := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, hrep, hcard]
      simp [tileFixedCount]

/-- **Fixed cylinder tilings of the reflection f, n even.** Let $T$ be a finite set of tile
designs, let $\sigma$ be a permutation of $T$ with $\sigma^2 = 1$, and let $n, m \ge 1$ with $n$
even. For $a \in \mathbb{Z}/n\mathbb{Z}$ count the tilings
$F : \mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z} \to T$ with
$F(-1 - x - a, y) = \sigma(F(x, y))$ for every cell $(x, y)$, and let $N$ be the sum of these
counts over all $a \in \mathbb{Z}/n\mathbb{Z}$. If $t_f$ is the number of designs $d \in T$ with
$\sigma(d) = d$, then
$$2N = n\left(|T|^{nm/2} + |T|^{(nm - 2m)/2} t_f^{2m}\right).$$

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 30. -/
public theorem cylinder_f_even {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1)
    (hn : Even n) :
    2 * cylinderShiftSum n m (cellF n m) σ =
      n * (Fintype.card T ^ (n * m / 2) +
        Fintype.card T ^ ((n * m - 2 * m) / 2) * tileFixedCount σ 1 ^ (2 * m)) := by
  classical
  have htiles : Function.Involutive σ := fun t => by
    simpa [sq] using DFunLike.congr_fun hσ t
  let A := Fintype.card T ^ (n * m / 2)
  let B := Fintype.card T ^ ((n * m - 2 * m) / 2) * tileFixedCount σ 1 ^ (2 * m)
  have hcount (a : ZMod n) :
      fixedTilingCount (fun c => cellF n m (c.1 + a, c.2)) σ =
        if Even a.val then A else B := by
    rw [fixedTilingCount_shiftedReflection n m a σ htiles, card_fixedColumns hn]
    split_ifs <;> simp [A, B]
  suffices hsum : 2 * (∑ a : ZMod n, if Even a.val then A else B) = n * (A + B) by
    simpa only [cylinderShiftSum, hcount] using hsum
  -- Index the two parities by the second coordinate of `Fin k × Fin 2`.
  obtain ⟨k, hk⟩ : ∃ k, n = k * 2 := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  let e : Fin k × Fin 2 ≃ ZMod n :=
    finProdFinEquiv.trans ((finCongr hk.symm).trans (ZMod.finEquiv n).toEquiv)
  have hfin (l : ℕ) [NeZero l] (i : Fin l) : (ZMod.finEquiv l i).val = i.val := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne l)
    rfl
  have he (i : Fin k × Fin 2) : (e i).val = i.1.val * 2 + i.2.val := by
    simp [e, hfin, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp [he, Fin.sum_univ_two, Nat.even_add_one, hk, Nat.mul_assoc, Nat.mul_left_comm]

/-- **Cylinder fixed-tiling count for the reflection $f$ when $n$ is odd.** Let $T$ be a finite set
of tile designs, let $n, m \ge 1$ with $n$ odd, and let $\sigma$ be a permutation of $T$ with
$\sigma^2 = 1$. Let $f$ be the cell map $(x, y) \mapsto (-1 - x, y)$ of
$\mathbb{Z}/n \times \mathbb{Z}/m$, and let $t$ be the number of designs fixed by $\sigma$. Then
the cylinder shift sum of $f$ and $\sigma$ equals $n \cdot |T|^{(nm - m)/2} \cdot t^m$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 30. -/
public theorem cylinder_f_odd {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1)
    (hn : Odd n) :
    cylinderShiftSum n m (cellF n m) σ =
      n * Fintype.card T ^ ((n * m - m) / 2) * tileFixedCount σ 1 ^ m := by
  classical
  have htiles : Function.Involutive σ := fun t => by
    simpa [sq] using DFunLike.congr_fun hσ t
  have hcount (a : ZMod n) :
      fixedTilingCount (fun c => cellF n m (c.1 + a, c.2)) σ =
        Fintype.card T ^ ((n * m - m) / 2) * tileFixedCount σ 1 ^ m := by
    let x₀ : ZMod n := (((n + 1) / 2 : ℕ) : ZMod n) * (-1 - a)
    have hmem (x : ZMod n) : -1 - x - a = x ↔ x = x₀ :=
      eq_comm.trans (by simpa only [Set.mem_ofPred_eq, Set.mem_singleton_iff, x₀]
        using Set.ext_iff.mp (reflection_shift_solutions_odd n a hn) x)
    have hcard : Fintype.card {x : ZMod n // -1 - x - a = x} = 1 :=
      (Fintype.card_congr (Equiv.subtypeEquivRight hmem)).trans (Fintype.card_subtype_eq x₀)
    rw [fixedTilingCount_shiftedReflection n m a σ htiles]
    simp only [hcard, one_mul]
  rw [cylinderShiftSum, Finset.sum_const_nat (fun a _ => hcount a)]
  simp only [Finset.card_univ, ZMod.card, Nat.mul_assoc]

end MetaMathlibExt
