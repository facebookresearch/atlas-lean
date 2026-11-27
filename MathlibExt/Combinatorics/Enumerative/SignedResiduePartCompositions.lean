/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.EvenOddCompositions
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Sym.Card

/-!
# Signed counts of compositions with parts in a residue class

The allowed parts are `k + s + r * b` for natural numbers `b`. For a fixed number of parts,
the offsets `b` form a weak composition of a prescribed total, counted by stars and bars.
The sign depends only on the number of parts.

## References

* Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal of Integer Sequences
  **27** (2024), Article 24.6.5, pp. 1–10, Theorem 10 (pp. 5–6).
  https://cs.uwaterloo.ca/journals/JIS/VOL27/Huang/huang9.html
-/

namespace MetaMathlibExt

private def residueOffset (k r s a : ℕ) : ℕ := (a - (k + s)) / r

private theorem residueOffset_add_mul {k r s b : ℕ} (hr : 0 < r) :
    residueOffset k r s (k + s + r * b) = b := by
  simp [residueOffset, hr]

-- After subtracting `k`, the remainder is `s`, so an admissible part cannot lie below `k + s`.
private theorem part_eq_add_mul_offset {k r s a : ℕ} (hsr : s < r)
    (ha : k ≤ a ∧ a % r = (k + s) % r) :
    k + s + r * residueOffset k r s a = a := by
  have hmod : k + (a - k) ≡ k + s [MOD r] := by
    simpa only [Nat.add_sub_of_le ha.1, Nat.ModEq] using ha.2
  have hrem : (a - k) % r = s :=
    (show (a - k) % r = s % r from Nat.ModEq.add_left_cancel' k hmod).trans
      (Nat.mod_eq_of_lt hsr)
  have hdiv : r * ((a - k) / r) + s = a - k := by
    simpa only [hrem] using Nat.div_add_mod (a - k) r
  have hsub : a - (k + s) = r * ((a - k) / r) := by omega
  rw [residueOffset, hsub, Nat.mul_div_cancel_left _ (by omega : 0 < r)]
  omega

private theorem sum_parts_eq {k r s : ℕ} (hsr : s < r) (l : List ℕ)
    (hl : ∀ a ∈ l, k ≤ a ∧ a % r = (k + s) % r) :
    l.length * (k + s) + r * (l.map (residueOffset k r s)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := part_eq_add_mul_offset hsr (hl a List.mem_cons_self)
    have ht := ih (fun b hb => hl b (List.mem_cons_of_mem a hb))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul, Nat.mul_add r]
    omega

private abbrev ResidueFiber (N k r s j i : ℕ) :=
  {c : Composition N // (∀ a ∈ c.blocks, k ≤ a ∧ a % r = (k + s) % r) ∧
    c.length = j + 1 ∧ (c.blocks.map (residueOffset k r s)).sum = i}

private abbrev OffsetVector (L i : ℕ) := {f : Fin L → ℕ // ∑ t, f t = i}

private def ofOffsets {N k r s j i : ℕ} (hk : 1 ≤ k) (hr : 0 < r)
    (hN : (j + 1) * (k + s) + r * i = N) (w : OffsetVector (j + 1) i) :
    ResidueFiber N k r s j i := by
  let blocks := List.ofFn fun t => k + s + r * w.val t
  have hparts (a : ℕ) (ha : a ∈ blocks) : k ≤ a ∧ a % r = (k + s) % r := by
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨by omega, by simp [Nat.mul_comm r]⟩
  have hsum : blocks.sum = N := by
    dsimp only [blocks]
    rw [List.sum_ofFn, Finset.sum_add_distrib, ← Finset.mul_sum, w.prop,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hN
  refine ⟨⟨blocks, fun ha => hk.trans (hparts _ ha).1, hsum⟩, hparts, List.length_ofFn, ?_⟩
  change (blocks.map (residueOffset k r s)).sum = i
  simpa only [blocks, List.map_ofFn, Function.comp_apply, residueOffset_add_mul hr, List.sum_ofFn]
    using w.prop

private theorem card_residueFiber {N k r s j i : ℕ} (hk : 1 ≤ k) (hsr : s < r)
    (hN : (j + 1) * (k + s) + r * i = N) :
    Nat.card (ResidueFiber N k r s j i) = (i + j).choose i := by
  classical
  have hr : 0 < r := by omega
  have hbij : Function.Bijective (ofOffsets hk hr hN) := by
    constructor
    · intro u v huv
      have h := congrArg (fun c : ResidueFiber N k r s j i => c.val.blocks) huv
      apply Subtype.ext
      funext t
      have ht := congrFun (List.ofFn_injective h) t
      simpa only [residueOffset_add_mul hr] using congrArg (residueOffset k r s) ht
    · intro c
      let f (t : Fin (j + 1)) := c.val.blocksFun (Fin.cast c.prop.2.1.symm t)
      have hf : List.ofFn f = c.val.blocks := by
        apply List.ext_getElem
        · simpa using c.prop.2.1.symm
        · intro t ht ht'
          simp only [List.getElem_ofFn, f, Composition.blocksFun, List.get_eq_getElem, Fin.val_cast]
      let w : OffsetVector (j + 1) i := ⟨fun t => residueOffset k r s (f t), by
        rw [← List.sum_ofFn]
        change (List.ofFn (residueOffset k r s ∘ f)).sum = i
        rw [← List.map_ofFn, hf]
        exact c.prop.2.2⟩
      refine ⟨w, Subtype.ext (Composition.ext ?_)⟩
      change List.ofFn (fun t => k + s + r * residueOffset k r s (f t)) = c.val.blocks
      rw [← hf]
      exact congrArg List.ofFn (funext fun t =>
        part_eq_add_mul_offset hsr (c.prop.1 _ (c.val.blocksFun_mem_blocks _)))
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij),
    Nat.card_congr (Sym.equivNatSumOfFintype (Fin (j + 1)) i).symm,
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show j + 1 + i - 1 = i + j by omega]

/-- **Signed count of compositions with parts at least $k$ in a residue class.** Let $k, n \ge 1$
and $r > s \ge 0$. Among the compositions of $n + k - 1$ whose parts are all at least $k$ and
congruent to $k + s$ modulo $r$, the number with an odd number of parts minus the number with an
even number of parts is the sum of $(-1)^j \binom{i+j}{i}$ over all $i, j \ge 0$ with
$ri + j(k+s) + s + 1 = n$ (an empty sum when $n \le s$).

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 10
(`jis-2024-24.6.5-thm-10`). -/
public theorem compositionOddMinusEven_parts_ge_modEq (k n r s : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) (hsr : s < r) :
    compositionOddMinusEven (n + k - 1)
        (fun c => ∀ a ∈ c.blocks, k ≤ a ∧ a % r = (k + s) % r)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if r * i + j * (k + s) + s + 1 = n then (-1 : ℤ) ^ j * ((i + j).choose i : ℤ)
          else 0 := by
  classical
  let N := n + k - 1
  let P (c : Composition N) := ∀ a ∈ c.blocks, k ≤ a ∧ a % r = (k + s) % r
  let _ : DecidablePred P := fun _ => Classical.propDecidable _
  let u := Finset.univ.filter P
  let t := Finset.range (n + 1)
  let key (c : Composition N) := ((c.blocks.map (residueOffset k r s)).sum, c.length - 1)
  have hpos (c : Composition N) : 0 < c.length :=
    c.length_pos_iff.mpr (by dsimp [N]; omega)
  have hweight (c : Composition N) (hc : P c) :
      r * (key c).1 + (key c).2 * (k + s) + s + 1 = n := by
    have h := sum_parts_eq hsr c.blocks hc
    change c.length * (k + s) + r * (key c).1 = c.blocks.sum at h
    have hlen : c.length = (key c).2 + 1 := by dsimp [key]; have := hpos c; omega
    rw [hlen, Nat.add_mul, Nat.one_mul, c.blocks_sum] at h
    dsimp [N] at h
    omega
  have hmaps : ∀ c ∈ u, key c ∈ t ×ˢ t := by
    intro c hc
    have hw := hweight c (Finset.mem_filter.mp hc).2
    have hi : (key c).1 ≤ r * (key c).1 := by
      simpa using Nat.mul_le_mul_right (key c).1 (show 1 ≤ r by omega)
    have hj : (key c).2 ≤ (key c).2 * (k + s) := by
      simpa using Nat.mul_le_mul_left (key c).2 (show 1 ≤ k + s by omega)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩
  change compositionOddMinusEven N P = _
  calc
    _ = ∑ c ∈ u, (-1 : ℤ) ^ (key c).2 := by
      rw [compositionOddMinusEven, ← Finset.sum_filter (s := Finset.univ) P
        (fun c => (-1 : ℤ) ^ (c.length + 1))]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show c.length + 1 = (key c).2 + 2 by dsimp [key]; have := hpos c; omega, pow_add]
      simp
    _ = ∑ p ∈ t ×ˢ t, ∑ _c ∈ u.filter (fun c => key c = p), (-1 : ℤ) ^ p.2 :=
      (Finset.sum_fiberwise_of_maps_to' hmaps fun p => (-1 : ℤ) ^ p.2).symm
    _ = ∑ p ∈ t ×ˢ t, if r * p.1 + p.2 * (k + s) + s + 1 = n then
          (-1 : ℤ) ^ p.2 * ((p.1 + p.2).choose p.1 : ℤ) else 0 := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ -
      by_cases hij : r * i + j * (k + s) + s + 1 = n
      · have hN : (j + 1) * (k + s) + r * i = N := by
          rw [Nat.add_mul, Nat.one_mul]
          dsimp [N]
          omega
        have hfiber : u.filter (fun c => key c = (i, j)) =
            Finset.univ.filter (fun c : Composition N => P c ∧ c.length = j + 1 ∧
              (c.blocks.map (residueOffset k r s)).sum = i) := by
          ext c
          simp only [u, key, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
          have := hpos c
          exact and_congr_right fun _ => by omega
        have hcard : (u.filter (fun c => key c = (i, j))).card = (i + j).choose i := by
          rw [hfiber, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
          exact card_residueFiber hk hsr hN
        simp only [hij, ite_true, Finset.sum_const, nsmul_eq_mul, hcard]
        exact mul_comm _ _
      · have hempty : u.filter (fun c => key c = (i, j)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro c hc
          obtain ⟨hc, hkey⟩ := Finset.mem_filter.mp hc
          have hw := hweight c (Finset.mem_filter.mp hc).2
          rw [hkey] at hw
          exact hij hw
        simp [hempty, hij]
    _ = _ := Finset.sum_product ..

end MetaMathlibExt
