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
import Mathlib.Data.Sym.Card

/-!
# Signed counts of compositions with a minimum part size

Group compositions by their number of parts. Subtracting the minimum size from each part
leaves a weak composition, counted by stars and bars. The sign is constant within each group.
-/

namespace MetaMathlibExt

private abbrev MinPartFiber (N k L : ℕ) :=
  {c : Composition N // (∀ a ∈ c.blocks, k ≤ a) ∧ c.length = L}

private abbrev Slack (L M : ℕ) := {f : Fin L → ℕ // ∑ i, f i = M}

private def addMinPart {N k L : ℕ} (hk : 1 ≤ k) (hL : L * k ≤ N)
    (w : Slack L (N - L * k)) : MinPartFiber N k L := by
  let blocks := List.ofFn fun i => w.val i + k
  have hparts (a : ℕ) (ha : a ∈ blocks) : k ≤ a := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.le_add_left ..
  have hsum : blocks.sum = N := by
    simp [blocks, List.sum_ofFn, Finset.sum_add_distrib, w.prop, Nat.sub_add_cancel hL]
  exact ⟨⟨blocks, fun ha => hk.trans (hparts _ ha), hsum⟩, hparts, List.length_ofFn⟩

-- Subtracting k from each block gives a weak composition of the remaining total.
private theorem card_minPartFiber {N k j : ℕ} (hk : 1 ≤ k) (hL : (j + 1) * k ≤ N) :
    Nat.card (MinPartFiber N k (j + 1)) = (N - (j + 1) * k + j).choose j := by
  classical
  let M := N - (j + 1) * k
  have hbij : Function.Bijective (addMinPart hk hL) := by
    constructor
    · intro u v huv
      have hb := congrArg (fun c : MinPartFiber N k (j + 1) => c.val.blocks) huv
      apply Subtype.ext
      funext i
      exact Nat.add_right_cancel (congrFun (List.ofFn_injective hb) i)
    · intro c
      let f (i : Fin (j + 1)) := c.val.blocksFun (Fin.cast c.prop.2.symm i)
      have hf : List.ofFn f = c.val.blocks := by
        apply List.ext_getElem
        · simpa using c.prop.2.symm
        · intro i hi hi'
          simp only [List.getElem_ofFn, f, Composition.blocksFun, List.get_eq_getElem, Fin.val_cast]
      have hparts (i : Fin (j + 1)) : k ≤ f i :=
        c.prop.1 _ (c.val.blocksFun_mem_blocks _)
      let w : Slack (j + 1) M := ⟨fun i => f i - k, by
        rw [Finset.sum_tsub_distrib _ (fun i _ => hparts i), ← List.sum_ofFn, hf,
          c.val.blocks_sum]
        simp [M]⟩
      refine ⟨w, Subtype.ext (Composition.ext ?_)⟩
      change List.ofFn (fun i => f i - k + k) = c.val.blocks
      rw [← hf]
      exact congrArg List.ofFn (funext fun i => Nat.sub_add_cancel (hparts i))
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij),
    Nat.card_congr (Sym.equivNatSumOfFintype (Fin (j + 1)) M).symm,
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show j + 1 + M - 1 = M + j by omega, Nat.choose_symm_add]

/-- **Signed count of compositions with parts at least $k$.** Let $k, n \ge 1$. Among the
compositions of $n + k - 1$ whose parts are all at least $k$, the number with an odd number of
parts minus the number with an even number of parts equals
$\sum_{j=0}^{\lfloor (n-1)/k \rfloor} (-1)^j \binom{n-1-j(k-1)}{j}$.

Source: Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal
of Integer Sequences 27 (2024), Article 24.6.5, Theorem 8
(`jis-2024-24.6.5-thm-8`). -/
public theorem compositionOddMinusEven_parts_ge (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    compositionOddMinusEven (n + k - 1) (fun c => ∀ a ∈ c.blocks, k ≤ a)
      = ∑ j ∈ Finset.range ((n - 1) / k + 1),
          (-1 : ℤ) ^ j * ((n - 1 - j * (k - 1)).choose j : ℤ) := by
  classical
  let N := n + k - 1
  let P (c : Composition N) := ∀ a ∈ c.blocks, k ≤ a
  let _ : DecidablePred P := fun _ => Classical.propDecidable _
  let s := Finset.univ.filter P
  let t := Finset.range ((n - 1) / k + 1)
  have hpos (c : Composition N) : 0 < c.length :=
    c.length_pos_iff.mpr (by dsimp [N]; omega)
  have hmaps : ∀ c ∈ s, c.length - 1 ∈ t := by
    intro c hc
    have hp : P c := (Finset.mem_filter.mp hc).2
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin c.length => k) (g := c.blocksFun)
      (fun i _ => hp _ (c.blocksFun_mem_blocks i))
    have hle : c.length * k ≤ N := by simpa using hsum
    have h := hpos c
    have heq : c.length = (c.length - 1) + 1 := by omega
    conv at hle => lhs; rw [heq, Nat.add_mul, Nat.one_mul]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by omega)).mpr
      (by dsimp [N] at hle; omega)))
  change compositionOddMinusEven N P = ∑ j ∈ t, _
  calc
    _ = ∑ c ∈ s, (-1 : ℤ) ^ (c.length - 1) := by
      rw [compositionOddMinusEven, ← Finset.sum_filter (s := Finset.univ) P
        (fun c => (-1 : ℤ) ^ (c.length + 1))]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show c.length + 1 = c.length - 1 + 2 by have := hpos c; omega, pow_add]
      simp
    _ = ∑ j ∈ t, ∑ _c ∈ s.filter (fun c => c.length - 1 = j), (-1 : ℤ) ^ j :=
      (Finset.sum_fiberwise_of_maps_to' hmaps fun j => (-1 : ℤ) ^ j).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j * k ≤ n - 1 := (Nat.le_div_iff_mul_le (by omega)).mp
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      have hL : (j + 1) * k ≤ N := by rw [Nat.add_mul, Nat.one_mul]; dsimp [N]; omega
      have hfiber : s.filter (fun c => c.length - 1 = j) =
          Finset.univ.filter (fun c : Composition N => P c ∧ c.length = j + 1) := by
        ext c
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        have := hpos c
        exact and_congr_right fun _ => by omega
      have hcard : (Finset.univ.filter (fun c : Composition N => P c ∧ c.length = j + 1)).card =
          Nat.card (MinPartFiber N k (j + 1)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hprod : j * k = j * (k - 1) + j := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
      have htop : N - (j + 1) * k + j = n - 1 - j * (k - 1) := by
        rw [Nat.add_mul, Nat.one_mul, hprod]
        dsimp [N]
        omega
      rw [Finset.sum_const, nsmul_eq_mul, hfiber, hcard, card_minPartFiber hk hL, htop, mul_comm]

end MetaMathlibExt
