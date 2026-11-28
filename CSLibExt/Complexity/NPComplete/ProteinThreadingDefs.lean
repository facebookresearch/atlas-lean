/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROTEIN THREADING: definitions

Source:
R. H. Lathrop, "The protein threading problem with sequence amino acid interaction preferences
is NP-complete", Protein Engineering 7 (1994), 1059-1068, doi:10.1093/protein/7.9.1059,
Appendix, "A formal problem statement (PRO-THREAD)", equations (1)-(4).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProteinThreading

/-- An integer `p - q`, written as the pair `(p, q)`. -/
abbrev IntCode := ℕ × ℕ

/-- An instance: the core segments (segment `i` lists the vertex labels of `C_{i,1}, …, C_{i,cᵢ}`),
the edges `((i, j), (i', j'), d)` from tail `C_{i,j}` to head `C_{i',j'}` with edge label `d`, the
sequence `a`, the score tables for `σ_v` (keys `(character, vertex label)`), `σ_e` (keys
`(head character, tail character, edge label)`) and `σ_l` (keys: contiguous subsequences of `a`),
and `K`. -/
abbrev ProteinThreadingInstance :=
  List (List ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ) × List ℕ × List ((ℕ × ℕ) × IntCode) ×
    List ((ℕ × ℕ × ℕ) × IntCode) × List (List ℕ × IntCode) × IntCode

/-- The integer written as `(p, q)`. -/
def IntCode.val (z : IntCode) : ℤ := (z.1 : ℤ) - z.2

/-- The value of a score table at `k`: the listed value, or `0` if `k` is not listed. -/
def tableScore {κ : Type} [DecidableEq κ] (tbl : List (κ × IntCode)) (k : κ) : ℤ :=
  match tbl.lookup k with
  | some z => z.val
  | none => 0

/-- The contiguous subsequence `a[x, y)` of `a` (0-based, `y` excluded). -/
def segment (a : List ℕ) (x y : ℕ) : List ℕ :=
  (a.drop x).take (y - x)

/-- `C_{i,j}` (0-based) is a vertex: `i < m` and `j < cᵢ`. -/
def IsVertex (segs : List (List ℕ)) (v : ℕ × ℕ) : Prop :=
  v.1 < segs.length ∧ v.2 < (segs.getD v.1 []).length

/-- Well-formedness: a nonempty partition into nonempty core segments; directed edges between
vertices, without loops, at most one per ordered pair; amino acids `0, …, 19`; score tables with
distinct keys, characters among the amino acids, and `σ_l` keys contiguous subsequences of `a`. -/
def WellFormed : ProteinThreadingInstance → Prop
  | (segs, edges, a, σv, σe, σl, _) =>
    segs ≠ [] ∧ (∀ c ∈ segs, c ≠ []) ∧
    (∀ e ∈ edges, IsVertex segs e.1 ∧ IsVertex segs e.2.1 ∧ e.1 ≠ e.2.1) ∧
    (edges.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ x ∈ a, x < 20) ∧
    (σv.map Prod.fst).Nodup ∧ (∀ k ∈ σv, k.1.1 < 20) ∧
    (σe.map Prod.fst).Nodup ∧ (∀ k ∈ σe, k.1.1 < 20 ∧ k.1.2.1 < 20) ∧
    (σl.map Prod.fst).Nodup ∧ ∀ k ∈ σl, k.1 <:+: a

/-- `t` is a threading: `m` starting positions with `tᵢ + cᵢ ≤ tᵢ₊₁` for consecutive segments and
`tₘ + cₘ ≤ n` (0-based positions). -/
def IsThreading (segs : List (List ℕ)) (a : List ℕ) (t : List ℕ) : Prop :=
  t.length = segs.length ∧
    (∀ i, i + 1 < segs.length → t.getD i 0 + (segs.getD i []).length ≤ t.getD (i + 1) 0) ∧
    t.getD (segs.length - 1) 0 + (segs.getD (segs.length - 1) []).length ≤ a.length

/-- `π(v, t)`: the character of `a` threaded into the vertex `v = C_{i,j}`, namely `a[tᵢ + j]`. -/
def threaded (a t : List ℕ) (v : ℕ × ℕ) : ℕ :=
  a.getD (t.getD v.1 0 + v.2) 0

/-- `f(t)`, Lathrop's equation (4): the vertex scores (1), the edge scores (2) and the loop scores
(3). Loop region `i ∈ {0, …, m}` runs from the end of segment `i - 1` (from `0` when `i = 0`) to the
start of segment `i` (to `n` when `i = m`). -/
def score : ProteinThreadingInstance → List ℕ → ℤ
  | (segs, edges, a, σv, σe, σl, _), t =>
    ((List.range segs.length).map fun i =>
        ((List.range (segs.getD i []).length).map fun j =>
          tableScore σv (threaded a t (i, j), (segs.getD i []).getD j 0)).sum).sum +
      (edges.map fun e => tableScore σe (threaded a t e.2.1, threaded a t e.1, e.2.2)).sum +
      ((List.range (segs.length + 1)).map fun i =>
        tableScore σl (segment a
          (if i = 0 then 0 else t.getD (i - 1) 0 + (segs.getD (i - 1) []).length)
          (if i = segs.length then a.length else t.getD i 0))).sum

/-- There is a threading `t` with `f(t) ≤ K`. -/
def ProteinThreadingFeasible (i : ProteinThreadingInstance) : Prop :=
  ∃ t : List ℕ, IsThreading i.1 i.2.2.1 t ∧ score i t ≤ i.2.2.2.2.2.2.val

open Classical in
/-- PROTEIN THREADING as a decision problem over bitstrings. -/
noncomputable def proteinThreadingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProteinThreadingInstance) x with
  | some i => decide (WellFormed i ∧ ProteinThreadingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ProteinThreading
