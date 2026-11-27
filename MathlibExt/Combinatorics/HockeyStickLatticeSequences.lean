/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Powerset
public import MathlibExt.Combinatorics.HockeyStickTableauCardinality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic

/-! # Cardinality of labeled lattice sequences -/

namespace MetaMathlibExt

@[expose] public section

/-- The set `𝒞(k, r)` of compositions of some `j ≤ k` with every part in `[2, r + 1]`, as lists
of parts.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.2 (definition of `c(k, r)` and `𝒞(k, r)`). -/
def hockeyCompositions (k r : ℕ) : Finset (List ℕ) :=
  (Finset.range (k + 1)).biUnion fun j =>
    (Finset.range (j + 1)).biUnion fun l =>
      ((Finset.Nat.antidiagonalTuple l j).filter fun x => ∀ i, 2 ≤ x i ∧ x i ≤ r + 1).image
        List.ofFn

/-- The lattice sequences `𝓛(m, h)` of width `m` and height `h`:
`0 = L_0 ≤ L_1 ≤ ⋯ ≤ L_{m+1} = h`, as maps `Fin (m + 2) → Fin (h + 1)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Section 2.4 (lattice sequences). -/
def latticeSequences (m h : ℕ) : Finset (Fin (m + 2) → Fin (h + 1)) :=
  Finset.univ.filter fun L =>
    L 0 = 0 ∧ (∀ i : Fin (m + 1), L i.castSucc ≤ L i.succ) ∧ L (Fin.last (m + 1)) = Fin.last h

end

private theorem mem_latticeSequences {m h : ℕ} {L : Fin (m + 2) → Fin (h + 1)} :
    L ∈ latticeSequences m h ↔ L 0 = 0 ∧ Monotone L ∧ L (Fin.last (m + 1)) = Fin.last h := by
  simp [latticeSequences, Fin.monotone_iff_le_succ]

private def withEndpoints {m h : ℕ} (a : Fin m → Fin (h + 1)) : Fin (m + 2) → Fin (h + 1) :=
  Fin.lastCases (Fin.last h) (Fin.cases 0 a)

private theorem withEndpoints_mem {m h : ℕ} {a : Fin m → Fin (h + 1)} (ha : Monotone a) :
    withEndpoints a ∈ latticeSequences m h := by
  have hzero : withEndpoints a 0 = 0 := by
    change withEndpoints a (Fin.castSucc 0) = 0
    simp only [withEndpoints, Fin.lastCases_castSucc, Fin.cases_zero]
  refine mem_latticeSequences.mpr ⟨hzero, ?_, by simp [withEndpoints]⟩
  intro i j
  refine Fin.lastCases (fun _ => ?_) (fun j hij => ?_) j
  · simpa [withEndpoints] using Fin.le_last (withEndpoints a i)
  revert hij
  refine Fin.lastCases (fun hij => ?_) (fun i hij => ?_) i
  · exact (not_le_of_gt (Fin.castSucc_lt_last j) hij).elim
  simp only [withEndpoints, Fin.lastCases_castSucc]
  revert hij
  refine Fin.cases (fun hij => ?_) (fun j hij => ?_) j
  · have hi : i = 0 := le_antisymm (Fin.castSucc_le_castSucc_iff.mp hij) (Fin.zero_le _)
    subst i
    rfl
  revert hij
  refine Fin.cases (fun _ => ?_) (fun i hij => ?_) i
  · simpa only [Fin.cases_zero] using Fin.zero_le (Fin.cases 0 a j.succ)
  simpa only [Fin.cases_succ] using
    ha (Fin.succ_le_succ_iff.mp (Fin.castSucc_le_castSucc_iff.mp hij))

-- Shift the interior entries by their zero-based indices to make them strictly increasing.
private def shiftInterior {m h : ℕ} (L : Fin (m + 2) → Fin (h + 1)) (i : Fin m) : Fin (m + h) :=
  ⟨(L i.succ.castSucc).val + i.val, by
    have hi := i.isLt
    have hL := (L i.succ.castSucc).isLt
    omega⟩

private theorem strictMono_shiftInterior {m h : ℕ} {L : Fin (m + 2) → Fin (h + 1)}
    (hL : Monotone L) : StrictMono (shiftInterior L) := by
  intro i j hij
  have hmono := hL (Fin.strictMono_castSucc.monotone (Fin.strictMono_succ.monotone hij.le))
  change (L i.succ.castSucc).val ≤ (L j.succ.castSucc).val at hmono
  change i.val < j.val at hij
  change (L i.succ.castSucc).val + i.val < (L j.succ.castSucc).val + j.val
  omega

private theorem index_le_of_strictMono {m N : ℕ} {f : Fin m → Fin N}
    (hf : StrictMono f) (i : Fin m) : i.val ≤ (f i).val := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hs : (f i.castSucc).val < (f i.succ).val := hf (by simp)
      change i.val ≤ (f i.castSucc).val at ih
      change i.val + 1 ≤ (f i.succ).val
      omega

private theorem card_latticeSequences (m h : ℕ) :
    (latticeSequences m h).card = (m + h).choose h := by
  let subsets := (Finset.univ : Finset (Fin (m + h))).powersetCard m
  have hcard : (latticeSequences m h).card = subsets.card := by
    refine Finset.card_bij (fun L _ => Finset.univ.image (shiftInterior L)) ?_ ?_ ?_
    · intro L hL
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_image_of_injective _
        (strictMono_shiftInterior (mem_latticeSequences.mp hL).2.1).injective,
        Finset.card_univ, Fintype.card_fin]
    · intro L hL L' hL' heq
      have hmonoL := strictMono_shiftInterior (mem_latticeSequences.mp hL).2.1
      have hmonoL' := strictMono_shiftInterior (mem_latticeSequences.mp hL').2.1
      have hshift : shiftInterior L = shiftInterior L' := by
        apply (hmonoL.range_inj_of_wellFoundedLT hmonoL').mp
        simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
          congrArg (fun s : Finset (Fin (m + h)) => (s : Set (Fin (m + h)))) heq
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact (mem_latticeSequences.mp hL).2.2.trans (mem_latticeSequences.mp hL').2.2.symm
      refine Fin.cases ?_ (fun i => ?_) i
      · exact (mem_latticeSequences.mp hL).1.trans (mem_latticeSequences.mp hL').1.symm
      apply Fin.ext
      have hi := congrArg (fun f : Fin m → Fin (m + h) => (f i).val) hshift
      change (L i.succ.castSucc).val + i.val = (L' i.succ.castSucc).val + i.val at hi
      omega
    · intro s hs
      -- The sorted enumeration of the subset recovers the shifted interior entries.
      have hsCard := (Finset.mem_powersetCard.mp hs).2
      let f := s.orderEmbOfFin hsCard
      let a (i : Fin m) := (f i).val - i.val
      have hmono : Monotone a := by
        cases m with
        | zero => exact fun {i} => Fin.elim0 i
        | succ m =>
          refine Fin.monotone_iff_le_succ.mpr fun i => ?_
          have hi : (f i.castSucc).val < (f i.succ).val := f.strictMono (by simp)
          change (f i.castSucc).val - i.val ≤ (f i.succ).val - (i.val + 1)
          omega
      have hab (i : Fin m) : a i < h + 1 := by
        let j : Fin m := ⟨m - 1, by have := i.isLt; omega⟩
        have hij : i ≤ j := by
          change i.val ≤ m - 1
          have := i.isLt
          omega
        have hj := (f j).isLt
        have hbound : a j < h + 1 := by
          change (f j).val - (m - 1) < h + 1
          omega
        exact lt_of_le_of_lt (hmono hij) hbound
      let interior (i : Fin m) : Fin (h + 1) := ⟨a i, hab i⟩
      refine ⟨withEndpoints interior, withEndpoints_mem hmono, ?_⟩
      have hshift : shiftInterior (withEndpoints interior) = f := by
        funext i
        apply Fin.ext
        have hi := index_le_of_strictMono f.strictMono i
        change (withEndpoints interior i.succ.castSucc).val + i.val = (f i).val
        simpa only [withEndpoints, Fin.lastCases_castSucc, Fin.cases_succ, interior, a] using
          Nat.sub_add_cancel hi
      rw [hshift]
      exact s.image_orderEmbOfFin_univ hsCard
  rw [hcard]
  simpa [subsets] using (Nat.choose_symm_add (a := m) (b := h))

private theorem sum_le_of_mem_hockeyCompositions {k r : ℕ} {α : List ℕ}
    (hα : α ∈ hockeyCompositions k r) : α.sum ≤ k := by
  unfold hockeyCompositions at hα
  obtain ⟨j, hj, hα⟩ := Finset.mem_biUnion.mp hα
  obtain ⟨l, _, hα⟩ := Finset.mem_biUnion.mp hα
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hα
  rw [List.sum_ofFn, Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hx).1]
  have hj' := Finset.mem_range.mp hj
  omega

public section

/-- For `α ∈ 𝒞(k, r)`, the number of labeled lattice sequences `(λ, L)` of type `(k, n, r)` with
`sh(λ) = α` (`λ ∈ Λ(α, r)`, `L ∈ 𝓛(rk + n + 1 + ℓ(α), k - |α|)`) is
`(∏_j C(r, α_j - 1)) · C((r + 1)k + n + 1 - |α| + ℓ(α), k - |α|)`.

Source: Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, Journal of
Integer Sequences 28 (2025), Article 25.7.7, Proposition 11 (`jis-2025-25.7.7-prop-11`). -/
theorem card_labeledLatticeSequences (k n r : ℕ) (α : List ℕ)
    (hα : α ∈ hockeyCompositions k r) :
    (labeledTableaux α r ×ˢ latticeSequences (r * k + n + 1 + α.length) (k - α.sum)).card =
      (α.map fun a => r.choose (a - 1)).prod *
        ((r + 1) * k + n + 1 - α.sum + α.length).choose (k - α.sum) := by
  have hsum := sum_le_of_mem_hockeyCompositions hα
  have htop : r * k + n + 1 + α.length + (k - α.sum) =
      (r + 1) * k + n + 1 - α.sum + α.length := by
    rw [Nat.succ_mul]
    omega
  rw [Finset.card_product, card_labeledTableaux, card_latticeSequences, htop]

end

end MetaMathlibExt
