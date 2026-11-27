/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FixedColumnHooks
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.List.Sort

/-!
# Fixed first-column hooks from a part of prescribed size

The generating function counts partitions by splitting their rows above and below the fixed hook.
-/

namespace MetaMathlibExt
namespace fixedFirstColumnHook_part_genFun

open Finset PowerSeries MathlibExt

private def prepend (a : ℕ) : List ℕ ↪ List ℕ where
  toFun := List.cons a
  inj' := fun {_ _} e => (List.cons.inj e).2

private theorem prepend_apply (a : ℕ) (l : List ℕ) : prepend a l = a :: l := rfl

/-- Decreasing row lists in a rectangle, including padding by zeros. -/
private def box : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | r + 1, 0 => {List.replicate (r + 1) 0}
  | r + 1, w + 1 => box (r + 1) w ∪
      (box r (w + 1)).map (prepend (w + 1))

private theorem mem_box (r w : ℕ) (l : List ℕ) :
    l ∈ box r w ↔ l.length = r ∧ l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, x ≤ w := by
  induction r generalizing w l with
  | zero => cases l <;> simp [box]
  | succ r ihr =>
    induction w generalizing l with
    | zero =>
      simp only [box, mem_singleton]
      constructor
      · rintro rfl
        simp [List.pairwise_replicate]
      · rintro ⟨hl, _, hm⟩
        exact List.eq_replicate_iff.mpr ⟨hl, fun x hx => Nat.le_zero.mp (hm x hx)⟩
    | succ w ihw =>
      cases l with
      | nil => simp [box, ihw, prepend_apply]
      | cons a l =>
        simp only [box, mem_union, ihw, mem_map, prepend_apply, List.cons.injEq,
          List.length_cons, Nat.succ.injEq, List.pairwise_cons, List.forall_mem_cons]
        constructor
        · rintro (⟨hl, hs, ha, hb⟩ | ⟨t, ht, e, rfl⟩)
          · exact ⟨hl, hs, by omega, fun x hx => (hb x hx).trans (by omega)⟩
          · obtain ⟨hl, hs, hb⟩ := (ihr _ _).mp ht
            exact ⟨hl, ⟨by simpa [← e] using hb, hs⟩, by omega, hb⟩
        · rintro ⟨hl, ⟨ha, hs⟩, haw, hb⟩
          by_cases e : a = w + 1
          · exact Or.inr ⟨l, (ihr _ _).mpr ⟨hl, hs, hb⟩, e.symm, rfl⟩
          · exact Or.inl ⟨hl, ⟨ha, hs⟩, by omega, fun x hx => (ha x hx).trans (by omega)⟩

private theorem sum_box (r w : ℕ) :
    ∑ l ∈ box r w, (X : ℚ⟦X⟧) ^ l.sum = gaussBinom X (r + w) w := by
  induction r generalizing w with
  | zero => simp [box]
  | succ r ihr =>
    induction w with
    | zero => simp [box, List.sum_replicate]
    | succ w ihw =>
      rw [box, sum_union, sum_map, show r + 1 + (w + 1) = (r + 1 + w) + 1 by omega,
        gaussBinom_succ_succ]
      · simp only [prepend_apply, List.sum_cons, pow_add, ← mul_sum, ihr, ihw,
          show r + (w + 1) = r + 1 + w by omega]
      · refine disjoint_left.mpr fun l hl hmap => ?_
        obtain ⟨t, _, rfl⟩ := mem_map.mp hmap
        have := ((mem_box _ _ _).mp hl).2.2 (w + 1) List.mem_cons_self
        omega

/-- An upper width bound of `n` is invisible through degree `n`. -/
private theorem coeff_box_stable (r n : ℕ) (f : ℚ⟦X⟧) :
    coeff n (f * gaussBinom X (r + n) n) = coeff n (f * (qPochFin X r)⁻¹) := by
  let I : Ideal ℚ⟦X⟧ := Ideal.span {(X : ℚ⟦X⟧) ^ (n + 1)}
  let F := Ideal.Quotient.mk I
  have hx : F X ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have htail : F (qPochFin X (r + n)) = F (qPochFin X n) := by
    induction r with
    | zero => simp
    | succ i ih =>
      rw [Nat.succ_add, qPochFin_succ, map_mul, ih, map_sub, map_one, map_pow,
        pow_eq_zero_of_le (show n + 1 ≤ i + n + 1 by omega) hx, sub_zero, mul_one]
  have hg := gaussBinom_mul_qPochFin_mul_qPochFin (X : ℚ⟦X⟧) (r + n) n (by omega)
  simp only [Nat.add_sub_cancel] at hg
  have hu (j : ℕ) := PowerSeries.mul_inv_cancel (qPochFin (X : ℚ⟦X⟧) j)
    (by simp [qPochFin, map_prod])
  have he : F (gaussBinom X (r + n) n) = F ((qPochFin X r)⁻¹) := by
    have e := congrArg F hg
    rw [map_mul, map_mul, htail] at e
    have hn := map_mul_eq_one F (hu n)
    have hr := map_mul_eq_one F (hu r)
    apply left_inv_eq_right_inv _ hr
    apply (IsUnit.of_mul_eq_one _ hn).mul_right_cancel
    rwa [one_mul, mul_right_comm]
  have e : F (f * gaussBinom X (r + n) n) = F (f * (qPochFin X r)⁻¹) := by
    rw [map_mul, map_mul, he]
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp e)
  simpa only [map_sub, sub_eq_zero] using X_pow_dvd_iff.mp hd n (by omega)

/-- Read a row of the sorted list using the definition by column lengths. -/
private theorem row_at {n a : ℕ} (p : n.Partition) (u v : List ℕ)
    (hp : p.parts = ↑(u ++ a :: v)) (hu : ∀ x ∈ u, a ≤ x) (hv : ∀ x ∈ v, x ≤ a) :
    partitionRowLen p (u.length + 1) = a := by
  have han : a ≤ n := Nat.Partition.le_of_mem_parts (p := p) (by simp [hp])
  have cols : ((Icc 1 n).filter (fun j => u.length + 1 ≤ partitionColLen p j)) = Icc 1 a := by
    ext j
    simp only [mem_filter, mem_Icc]
    unfold partitionColLen
    rw [hp, Multiset.filter_coe, Multiset.coe_card, List.filter_append, List.length_append]
    by_cases hj : j ≤ a
    · have e : u.filter (fun b => decide (j ≤ b)) = u :=
        List.filter_eq_self.mpr fun b hb => decide_eq_true (hj.trans (hu b hb))
      simp [e, hj, hj.trans han]
    · have e : v.filter (fun b => decide (j ≤ b)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb h => hj ((of_decide_eq_true h).trans (hv b hb))
      simp [hj, e, List.length_filter_le]
  rw [partitionRowLen, cols, Nat.card_Icc]
  omega

private theorem col_one {n : ℕ} (p : n.Partition) : partitionColLen p 1 = p.parts.card := by
  rw [partitionColLen, Multiset.filter_eq_self.mpr (fun x hx => show 1 ≤ x from p.parts_pos hx)]

private def rows (k : ℕ) (uv : List ℕ × List ℕ) : List ℕ :=
  uv.1.map (· + k) ++ k :: uv.2.map (· + 1)

private theorem rows_pos {k : ℕ} (hk : 1 ≤ k) (uv : List ℕ × List ℕ) :
    ∀ x ∈ rows k uv, 1 ≤ x := by
  simp only [rows, List.mem_append, List.mem_cons, List.mem_map]
  rintro x (⟨a, _, rfl⟩ | rfl | ⟨a, _, rfl⟩) <;> omega

private theorem rows_sorted {r w s k : ℕ} (hk : 1 ≤ k) {u v : List ℕ}
    (hu : u ∈ box r w) (hv : v ∈ box s (k - 1)) :
    (rows k (u, v)).Pairwise (· ≥ ·) := by
  obtain ⟨_, hsu, _⟩ := (mem_box _ _ _).mp hu
  obtain ⟨_, hsv, hkv⟩ := (mem_box _ _ _).mp hv
  have hlow : ∀ x ∈ v.map (· + 1), x ≤ k := by
    rintro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have := hkv a ha
    omega
  refine List.pairwise_append.mpr ⟨hsu.map _ (fun _ _ h => by omega),
    List.pairwise_cons.mpr ⟨hlow, hsv.map _ (fun _ _ h => by omega)⟩, ?_⟩
  intro a ha b hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_cons.mp hb with rfl | hb
  · omega
  · exact (hlow b hb).trans (by omega)

private theorem rows_sum (k : ℕ) (u v : List ℕ) :
    (rows k (u, v)).sum = (u.length + 1) * k + v.length + u.sum + v.sum := by
  simp [rows, List.sum_map_add, List.map_const', List.sum_replicate, add_mul]
  omega

private abbrev Shape := Σ _ : ℕ, List ℕ × List ℕ

/-- With `s` rows below the hook there are `s + d` rows above it, where `d = k - h - 1`. -/
private def shapes (n k d : ℕ) : Finset Shape :=
  (range (n + 1)).sigma (fun s => box (s + d) n ×ˢ box s (k - 1))

private theorem mem_shapes {n k d s : ℕ} {u v : List ℕ} :
    (⟨s, u, v⟩ : Shape) ∈ shapes n k d ↔ s ≤ n ∧ u ∈ box (s + d) n ∧ v ∈ box s (k - 1) := by
  simp [shapes]

private theorem weighted_shapes (n k d : ℕ) :
    ∑ t ∈ shapes n k d, (X : ℚ⟦X⟧) ^ (rows k t.2).sum =
      ∑ s ∈ range (n + 1), X ^ ((s + d + 1) * k + s) *
        gaussBinom X (s + d + n) n * gaussBinom X (s + (k - 1)) (k - 1) := by
  unfold shapes
  rw [← sum_sigma' _ _ (fun (_ : ℕ) uv => (X : ℚ⟦X⟧) ^ (rows k uv).sum)]
  apply sum_congr rfl
  intro s _
  rw [sum_product, ← sum_box, ← sum_box, mul_assoc, sum_mul, mul_sum]
  apply sum_congr rfl
  intro u hu
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [rows_sum, ((mem_box _ _ _).mp hu).1, ((mem_box _ _ _).mp hv).1]
  simp only [pow_add, mul_assoc]

private def qualifying (n k : ℕ) (h : ℤ) : Finset n.Partition :=
  univ.filter (fun p => ((Icc 1 n).filter (fun s =>
    IsFixedColumnHook p 1 s h ∧ partitionRowLen p s = k)).Nonempty)

private theorem qualifies_of_shape {n k d s : ℕ} {h : ℤ} (hk : 1 ≤ k)
    (hd : (d : ℤ) = k - h - 1) {u v : List ℕ}
    (hu : u ∈ box (s + d) n) (hv : v ∈ box s (k - 1))
    (p : n.Partition) (hp : p.parts = ↑(rows k (u, v))) : p ∈ qualifying n k h := by
  have hrow := row_at p (u.map (· + k)) (v.map (· + 1)) hp
    (by simp) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := ((mem_box _ _ _).mp hv).2.2 i hi
      omega)
  rw [List.length_map, ((mem_box _ _ _).mp hu).1] at hrow
  have hlen : (rows k (u, v)).length = s + d + (s + 1) := by
    simp [rows, ((mem_box _ _ _).mp hu).1, ((mem_box _ _ _).mp hv).1]
  have hcard : partitionColLen p 1 = s + d + (s + 1) := by
    rw [col_one, hp, Multiset.coe_card, hlen]
  have hsum := p.parts_sum
  rw [hp, Multiset.sum_coe] at hsum
  have hle := List.length_le_sum_of_one_le _ (rows_pos hk (u, v))
  rw [hlen, hsum] at hle
  refine mem_filter.mpr ⟨mem_univ _, s + d + 1, mem_filter.mpr
    ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ⟨by omega, le_rfl, hrow.ge.trans' hk, ?_⟩, hrow⟩⟩
  rw [partitionHookLength, hrow, hcard]
  omega

/-- Cut the sorted list at the qualifying row, removing the compulsory cells on each side. -/
private theorem exists_shape {n k d : ℕ} {h : ℤ} (hk : 1 ≤ k)
    (hd : (d : ℤ) = k - h - 1) (p : n.Partition) (hp : p ∈ qualifying n k h) :
    ∃ t ∈ shapes n k d, p.parts = ↑(rows k t.2) := by
  obtain ⟨r, hr⟩ := (mem_filter.mp hp).2
  obtain ⟨hrn, hhook, hrk⟩ := mem_filter.mp hr
  obtain ⟨hr, -, -, he⟩ := hhook
  rw [partitionHookLength, hrk, col_one] at he
  let l := p.parts.sort (· ≥ ·)
  have hl : (↑l : Multiset ℕ) = p.parts := Multiset.sort_eq ..
  have hlen : r ≤ l.length := by
    by_contra! hlt
    have hcard : p.parts.card < r := by simpa [← hl] using hlt
    have emp : ((Icc 1 n).filter (fun j => r ≤ partitionColLen p j)) = ∅ :=
      filter_eq_empty_iff.mpr fun j _ hj =>
        hcard.not_ge (hj.trans (Multiset.card_le_card (Multiset.filter_le _ _)))
    rw [partitionRowLen, emp, card_empty] at hrk
    omega
  let i := r - 1
  have hi : i < l.length := by dsimp [i]; omega
  let u := l.take i
  let v := l.drop (i + 1)
  let a := l[i]
  have hl' : u ++ a :: v = l := by
    simpa only [u, a, v, List.getElem_cons_drop hi] using List.take_append_drop i l
  have hparts : p.parts = ↑(u ++ a :: v) := by rw [hl', hl]
  have hs : (u ++ a :: v).Pairwise (· ≥ ·) := hl' ▸ Multiset.pairwise_sort p.parts (· ≥ ·)
  obtain ⟨hus, hvs, huv⟩ := List.pairwise_append.mp hs
  obtain ⟨hva, hvs⟩ := List.pairwise_cons.mp hvs
  have hua (x) (hx : x ∈ u) : a ≤ x := huv x hx a List.mem_cons_self
  have hui : u.length = i := List.length_take.trans (Nat.min_eq_left hi.le)
  have hur : u.length + 1 = r := by dsimp [i] at hui; omega
  have ha := row_at p u v hparts hua hva
  rw [hur, hrk] at ha
  have hcl : p.parts.card = u.length + (v.length + 1) := by simp [hparts]
  have hud : u.length = v.length + d := by omega
  have hvn : v.length ≤ n := by have := (mem_Icc.mp hrn).2; omega
  have hpos (x) (hx : x ∈ v) : 1 ≤ x := p.parts_pos (by simp [hparts, hx])
  let upper := u.map (· - k)
  let lower := v.map (· - 1)
  have hu : upper ∈ box (v.length + d) n := by
    refine (mem_box _ _ _).mpr ⟨by simpa [upper] using hud,
      hus.map _ (fun _ _ e => Nat.sub_le_sub_right e _), ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hyn : y ≤ n := Nat.Partition.le_of_mem_parts (p := p) (by simp [hparts, hy])
    omega
  have hv : lower ∈ box v.length (k - 1) := by
    refine (mem_box _ _ _).mpr ⟨List.length_map _,
      hvs.map _ (fun _ _ e => Nat.sub_le_sub_right e _), ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Nat.sub_le_sub_right ((hva y hy).trans ha.ge) _
  have unshift (l : List ℕ) (b : ℕ) (hb : ∀ x ∈ l, b ≤ x) :
      (l.map (· - b)).map (· + b) = l := by
    simpa only [List.map_map] using (List.map_congr_left (f := (· + b) ∘ (· - b))
      (g := id) (fun x hx => Nat.sub_add_cancel (hb x hx))).trans (List.map_id _)
  refine ⟨⟨v.length, upper, lower⟩, mem_shapes.mpr ⟨hvn, hu, hv⟩, ?_⟩
  change p.parts = ↑(upper.map (· + k) ++ k :: lower.map (· + 1))
  rw [show upper.map (· + k) = u from unshift u k (fun x hx => ha.le.trans (hua x hx)),
    show lower.map (· + 1) = v from unshift v 1 hpos, ha]
  exact hparts

private theorem shapes_inj {n k d : ℕ} (hk : 1 ≤ k) {t t' : Shape}
    (ht : t ∈ shapes n k d) (ht' : t' ∈ shapes n k d)
    (he : (↑(rows k t.2) : Multiset ℕ) = ↑(rows k t'.2)) : t = t' := by
  obtain ⟨s, u, v⟩ := t
  obtain ⟨s', u', v'⟩ := t'
  obtain ⟨_, hu, hv⟩ := mem_shapes.mp ht
  obtain ⟨_, hu', hv'⟩ := mem_shapes.mp ht'
  have hl := List.Perm.eq_of_pairwise' (rows_sorted hk hu hv) (rows_sorted hk hu' hv')
    (Multiset.coe_eq_coe.mp he)
  have hlen := congrArg List.length hl
  simp only [rows, List.length_append, List.length_cons, List.length_map,
    ((mem_box _ _ _).mp hu).1, ((mem_box _ _ _).mp hv).1,
    ((mem_box _ _ _).mp hu').1, ((mem_box _ _ _).mp hv').1] at hlen
  have es : s = s' := by omega
  subst s'
  have hlu : (u.map (· + k)).length = (u'.map (· + k)).length := by
    simp [((mem_box _ _ _).mp hu).1, ((mem_box _ _ _).mp hu').1]
  obtain ⟨eu, ev⟩ := List.append_inj hl hlu
  have inj (a : ℕ) : Function.Injective (List.map (· + a) : List ℕ → List ℕ) :=
    List.map_injective_iff.mpr fun _ _ e => Nat.add_right_cancel e
  rw [show u = u' from inj k eu, show v = v' from inj 1 (List.cons.inj ev).2]

private theorem count_shapes (n k d : ℕ) (h : ℤ) (hk : 1 ≤ k) (hd : (d : ℤ) = k - h - 1) :
    ((qualifying n k h).card : ℚ) =
      coeff n (∑ t ∈ shapes n k d, (X : ℚ⟦X⟧) ^ (rows k t.2).sum) := by
  let S := (shapes n k d).filter (fun t => n = (rows k t.2).sum)
  let assemble (t : Shape) (ht : t ∈ S) : n.Partition :=
    ⟨↑(rows k t.2), fun hx => rows_pos hk t.2 _ hx,
      (Multiset.sum_coe _).trans (mem_filter.mp ht).2.symm⟩
  have e : S.card = (qualifying n k h).card := by
    apply card_bij assemble
    · rintro ⟨s, u, v⟩ ht
      obtain ⟨_, hu, hv⟩ := mem_shapes.mp (mem_filter.mp ht).1
      exact qualifies_of_shape hk hd hu hv _ rfl
    · intro t ht t' ht' e
      exact shapes_inj hk (mem_filter.mp ht).1 (mem_filter.mp ht').1
        (congrArg Nat.Partition.parts e)
    · intro p hp
      obtain ⟨t, ht, he⟩ := exists_shape hk hd p hp
      have hn := p.parts_sum
      rw [he, Multiset.sum_coe] at hn
      exact ⟨t, mem_filter.mpr ⟨ht, hn.symm⟩, Nat.Partition.ext he.symm⟩
  rw [← e, map_sum]
  simpa only [coeff_X_pow] using (sum_boole (R := ℚ)
    (fun t : Shape => n = (rows k t.2).sum) (shapes n k d)).symm

end fixedFirstColumnHook_part_genFun

open PowerSeries MathlibExt fixedFirstColumnHook_part_genFun

/-- **Partitions with a fixed first-column hook arising from a part of given size.** Let $n$ and $k$
be natural numbers with $k \ge 1$ and let $h < k$ be an integer. The number of partitions
$\lambda$ of $n$ that have an $h$-fixed hook in column $1$ at some row $s$ with $\lambda_s = k$ is
the coefficient of $q^n$ in
$$\sum_{s=0}^{n} \frac{q^{s(k+1)+k(k-h)}}{(q;q)_{s+k-h-1}} \binom{s+k-1}{k-1}_q,$$
where $(q;q)_j = \prod_{i<j} (1 - q^{i+1})$ is the finite $q$-Pochhammer symbol and
$\binom{a}{b}_q$ is the Gaussian binomial coefficient.

The $s$-th term has no monomial below $q^s$, so the count is also the coefficient of $q^n$ in the
full series over all $s \ge 0$. Under $s \mapsto s + k - h$ that series is the paper's
$\sum_{s \ge k-h} q^{(k+1)(s-1)+h+1} \binom{s+h-1}{k-1}_q / (q;q)_{s-1}$, whose lower limit
$k - h$ is a positive row index.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 6 (`integers-2025-A28-thm-6`). -/
public theorem fixedFirstColumnHook_part_genFun (n k : ℕ) (h : ℤ) (hk : 1 ≤ k)
    (hh : h < k) :
    (((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p 1 s h ∧ partitionRowLen p s = k)).Nonempty)).card : ℚ) =
      coeff n (∑ s ∈ Finset.range (n + 1),
        X ^ ((s : ℤ) * (k + 1) + k * (k - h)).toNat *
          (qPochFin (X : ℚ⟦X⟧) ((s : ℤ) + k - h - 1).toNat)⁻¹ *
          gaussBinom X (s + k - 1) (k - 1)) := by
  let d := ((k : ℤ) - h - 1).toNat
  have hd : (d : ℤ) = k - h - 1 := Int.toNat_of_nonneg (by omega)
  change ((qualifying n k h).card : ℚ) = _
  rw [count_shapes n k d h hk hd, weighted_shapes, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hexp : (s : ℤ) * (k + 1) + k * (k - h) = (((s + d + 1) * k + s : ℕ) : ℤ) := by
    push_cast
    rw [hd]
    ring
  have hden : (s : ℤ) + k - h - 1 = ((s + d : ℕ) : ℤ) := by omega
  rw [hexp, hden, Int.toNat_natCast, Int.toNat_natCast, show s + k - 1 = s + (k - 1) by omega]
  rw [mul_right_comm _ (gaussBinom X (s + d + n) n), mul_right_comm _ (qPochFin X (s + d))⁻¹]
  exact coeff_box_stable (s + d) n
    (X ^ ((s + d + 1) * k + s) * gaussBinom X (s + (k - 1)) (k - 1))

end MetaMathlibExt
