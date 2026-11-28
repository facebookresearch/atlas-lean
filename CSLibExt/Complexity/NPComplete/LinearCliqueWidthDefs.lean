/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR CLIQUE-WIDTH: definitions

Source:
M. R. Fellows, F. A. Rosamond, U. Rotics and S. Szeider, "Proving NP-hardness for clique-width
I: non-approximability of sequential clique-width", Electronic Colloquium on Computational
Complexity, Technical Report TR05-080, Revision 1 (2005),
https://eccc.weizmann.ac.il/report/2005/080/ (Section 3, the `r`-sequential clique-width and
footnote 1; Theorem 1, part 2, with `r = 1`);
F. Gurski and E. Wanke, "On the relationship between NLC-width and linear NLC-width",
Theoretical Computer Science 347(1-2) (2005), 76-89, doi:10.1016/j.tcs.2005.05.018 (linear
clique-width).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CliqueWidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearCliqueWidth

open MetaMathlibExt.Complexity.NPComplete.CliqueWidth
  (CliqueWidthInstance Generated Graph WellFormed)

/-- `LinearGenerated k V H l`: the graph `H` on `V` with vertex labels `l : V → Fin k` is the
value of a linear `k`-expression, one in which every disjoint union adds a single vertex. -/
inductive LinearGenerated (k : ℕ) : (V : Type) → SimpleGraph V → (V → Fin k) → Prop
  /-- `i(v)`: a single vertex with label `i`. -/
  | vertex (i : Fin k) : LinearGenerated k Unit ⊥ fun _ => i
  /-- `G ⊕ i(v)`: add a new vertex with label `i`, adjacent to nothing. -/
  | addVertex {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i : Fin k) :
      LinearGenerated k V G l →
        LinearGenerated k (V ⊕ Unit) (G ⊕g (⊥ : SimpleGraph Unit)) (Sum.elim l fun _ => i)
  /-- `η_{i,j}`, `i ≠ j`: join every vertex labelled `i` to every vertex labelled `j`. -/
  | join {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i j : Fin k) (hij : i ≠ j) :
      LinearGenerated k V G l →
        LinearGenerated k V (G ⊔ SimpleGraph.fromRel fun u v => l u = i ∧ l v = j) l
  /-- `ρ_{i→j}`: relabel every vertex labelled `i` to `j`. -/
  | relabel {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i j : Fin k) :
      LinearGenerated k V G l → LinearGenerated k V G fun v => if l v = i then j else l v

/-- Every linear `k`-expression is a `k`-expression: `addVertex i` is the union with the
single vertex `i(v)`. -/
theorem LinearGenerated.generated {k : ℕ} {V : Type} {H : SimpleGraph V} {l : V → Fin k}
    (h : LinearGenerated k V H l) : Generated k V H l := by
  induction h with
  | vertex i => exact .vertex i
  | addVertex i _ ih => exact .union ih (.vertex i)
  | join i j hij _ ih => exact .join i j hij ih
  | relabel i j _ ih => exact .relabel i j ih

/-- The linear clique-width of the graph is at most `K`: the graph is isomorphic to the graph of
some linear `K`-expression. -/
def LinearCliqueWidthFeasible (i : CliqueWidthInstance) : Prop :=
  ∃ (V : Type) (H : SimpleGraph V) (l : V → Fin i.2.2), LinearGenerated i.2.2 V H l ∧
    Nonempty (Graph i ≃g H)

open Classical in
/-- LINEAR CLIQUE-WIDTH as a decision problem over bitstrings. -/
noncomputable def linearCliqueWidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueWidthInstance) x with
  | some i => decide (WellFormed i ∧ LinearCliqueWidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LinearCliqueWidth
