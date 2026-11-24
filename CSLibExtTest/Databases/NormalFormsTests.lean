/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.NormalForms
public meta import CSLibExt.Databases.NormalForms
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.FinRange

/-!
# Tests for lossless decompositions and normal forms

Attributes `A, B, C = 0, 1, 2`, values natural numbers.
* Heath's theorem on a relation satisfying `A → B`; without the dependency the same decomposition
  loses information.
* The binary criterion: `{AB, AC}` is lossless for `A → B`, and `{AB, BC}` is not.
* `F = {AB → C, C → A}`: the scheme `ABC` is not in BCNF (`C → A`); the BCNF decomposition is
  `{AC, BC}`, both in BCNF, lossless, and (as is well known for this example) not
  dependency-preserving.
* Synthesis from `F` with the candidate key `BC` is lossless and dependency-preserving.
* For `G = {A → B, C → D}`, the dependency schemes `AB, CD` alone are lossy, and the synthesized
  decomposition with the key scheme `AC` is lossless.
* Satisfaction on a sub-schema is satisfaction of the projected dependencies: `{C → A}` imposes
  nothing on `AB`, whose decomposition into `A` and `B` is lossy.
* No BCNF decomposition of `Fdep` preserves dependencies (Abiteboul–Hull–Vianu, Example 11.2.10).
-/

@[expose] public section

namespace Cslib.Databases.NormalFormsTests

open Cslib.Databases

/-- The tuple with values `a`, `b`, `c` on `A`, `B`, `C`. -/
def tup (a b c : ℕ) : Tuple (Fin 3) ℕ := ![some a, some b, some c]

/-- A relation over `ABC` satisfying `A → B`. -/
def r : Finset (Tuple (Fin 3) ℕ) := {tup 1 2 3, tup 1 2 4, tup 2 5 3}

theorem r_isOver : IsOver Finset.univ r := by
  unfold IsOver Tuple.IsOver
  decide

example : join (project {0, 1} r) (project {0, 2} r) = r := by decide

example : join (project {0, 1} r) (project {0, 2} r) = r := by
  have hU : ({0, 1} ∪ {0, 2} : Finset (Fin 3)) = Finset.univ := by decide
  refine join_project_eq_of_holdsIn (hU ▸ r_isOver) ?_
  simp only [FD.HoldsIn, Finset.mem_coe]
  decide

/-- Without `A → B`, the decomposition into `AB` and `AC` is lossy. -/
example : join (project {0, 1} ({tup 1 2 3, tup 1 5 4} : Finset (Tuple (Fin 3) ℕ)))
    (project {0, 2} {tup 1 2 3, tup 1 5 4}) ≠ {tup 1 2 3, tup 1 5 4} := by
  decide

/-- `A → B`. -/
def FAB : Finset (FD (Fin 3)) := {⟨{0}, {1}⟩}

example : LosslessJoin ℕ FAB {0, 1} {0, 2} := losslessJoin_of_derives (Or.inl (by decide))

example : ¬ LosslessJoin ℕ FAB {0, 1} {1, 2} := by
  intro h
  have := derives_of_losslessJoin (d₀ := 0) (d₁ := 1) (by decide) (by decide) h
  revert this
  decide

/-- `F = {AB → C, C → A}`. -/
def F : Finset (FD (Fin 3)) := {⟨{0, 1}, {2}⟩, ⟨{2}, {0}⟩}

example : ¬ IsBCNF F Finset.univ := by decide

example : IsBCNF F {0, 2} ∧ IsBCNF F {1, 2} := by decide

#guard bcnfDecomposition F (List.finRange 3) Finset.univ == [{0, 2}, {1, 2}]

-- Repeated attributes in `l` do not multiply the candidates.
#guard (bcnfCandidates (List.replicate 30 (0 : Fin 3)) {0}).length == 2

example : ∀ T ∈ bcnfDecomposition F (List.finRange 3) Finset.univ, IsBCNF F T :=
  fun _ hT => isBCNF_of_mem_bcnfDecomposition F List.mem_finRange hT

/-- A relation over `ABC` satisfying `F`. -/
def s : Finset (Tuple (Fin 3) ℕ) := {tup 1 1 5, tup 1 2 5, tup 2 1 6}

theorem s_isOver : IsOver Finset.univ s := by
  unfold IsOver Tuple.IsOver
  decide

theorem s_satisfies : Satisfies (↑s : Set (Tuple (Fin 3) ℕ)) F := by
  simp only [Satisfies, FD.HoldsIn, Finset.mem_coe]
  decide

example : joinProjections (bcnfDecomposition F (List.finRange 3) Finset.univ) s = s :=
  bcnfDecomposition_lossless F _ s_isOver (s_satisfies.satisfiesOn _)

/-- The decomposition `{AC, BC}` does not preserve `AB → C`. -/
example : ¬ DependencyPreserving F [{0, 2}, {1, 2}] := by decide

example : findKey F (List.finRange 3) = {1, 2} := by decide

example : synthesize [⟨{0, 1}, {2}⟩, ⟨{2}, {0}⟩] {1, 2} = [{1, 2}, {0, 1, 2}, {0, 2}] := by
  decide

theorem F_equiv : Equivalent F ([⟨{0, 1}, {2}⟩, ⟨{2}, {0}⟩] : List (FD (Fin 3))).toFinset := by
  decide

example : DependencyPreserving F (synthesize [⟨{0, 1}, {2}⟩, ⟨{2}, {0}⟩] {1, 2}) :=
  synthesize_dependencyPreserving F_equiv _

example : joinProjections (synthesize [⟨{0, 1}, {2}⟩, ⟨{2}, {0}⟩] {1, 2}) s = s :=
  synthesize_lossless F_equiv (by decide) s_isOver s_satisfies

/-- `Fdep = {AB → C, C → B}` (AHV Example 11.2.10). -/
def Fdep : Finset (FD (Fin 3)) := {⟨{0, 1}, {2}⟩, ⟨{2}, {1}⟩}

/-- All proper subschemas of `ABC`. -/
private def properSchemas : Finset (Finset (Fin 3)) :=
  Finset.univ.powerset.erase Finset.univ

/-- Derivability is monotone in the dependency set. -/
private theorem derives_of_subset {F G : Finset (FD (Fin 3))} {f : FD (Fin 3)}
    (hFG : F ⊆ G) (h : Derives F f) : Derives G f := by
  induction h with
  | mem h => exact Derives.mem (hFG h)
  | refl h => exact Derives.refl h
  | augment Z _ ih => exact Derives.augment Z ih
  | trans _ _ ih₁ ih₂ => exact Derives.trans ih₁ ih₂

/-- Every dependency in a foldr-union of projected dependencies lies in one of the
projections. -/
private theorem exists_mem_projectFDs_of_mem_foldr {f : FD (Fin 3)}
    {M : List (Finset (Fin 3))}
    (h : f ∈ (M.map (projectFDs Fdep)).foldr (· ∪ ·) ∅) :
    ∃ S ∈ M, f ∈ projectFDs Fdep S := by
  induction M with
  | nil =>
    simp only [List.map_nil, List.foldr_nil, Finset.notMem_empty] at h
  | cons S M ih =>
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨S, List.mem_cons_self, h⟩
    · obtain ⟨T, hT, hf⟩ := ih h
      exact ⟨T, List.mem_cons_of_mem _ hT, hf⟩

/-- The full `ABC` schema is not in BCNF for `Fdep`. -/
private theorem not_isBCNF_univ : ¬ IsBCNF Fdep Finset.univ := by decide

/-- The union over all proper subschemas does not derive `AB → C`. -/
private theorem not_derives_saturated :
    ¬ Derives (properSchemas.biUnion (projectFDs Fdep)) ⟨{0, 1}, {2}⟩ := by
  decide

/-- **No BCNF decomposition preserves `Fdep`.** Every decomposition of `ABC` into BCNF
schemes loses a dependency of `Fdep` (in fact `AB → C`), so no dependency-preserving
BCNF decomposition of this schema exists. -/
theorem not_dependencyPreserving_of_isBCNF (L : List (Finset (Fin 3)))
    (hcover : schemaUnion L = Finset.univ) (hbcnf : ∀ S ∈ L, IsBCNF Fdep S) :
    ¬ DependencyPreserving Fdep L := by
  intro hpres
  have _ := hcover
  have hmem : ∀ S ∈ L, S ∈ properSchemas := by
    intro S hS
    simp only [properSchemas, Finset.mem_erase, Finset.mem_powerset]
    refine ⟨?_, Finset.subset_univ S⟩
    rintro rfl
    exact not_isBCNF_univ (hbcnf _ hS)
  have hsub : (L.map (projectFDs Fdep)).foldr (· ∪ ·) ∅ ⊆
      properSchemas.biUnion (projectFDs Fdep) := by
    intro f hf
    obtain ⟨S, hS, hfS⟩ := exists_mem_projectFDs_of_mem_foldr hf
    exact Finset.mem_biUnion.mpr ⟨S, hmem S hS, hfS⟩
  have hAB : ⟨{0, 1}, {2}⟩ ∈ Fdep := by decide
  exact not_derives_saturated (derives_of_subset hsub (hpres _ hAB))

/-! ### The key scheme matters -/

/-- `G = {A → B, C → D}` over `A, B, C, D = 0, 1, 2, 3`. -/
def G : Finset (FD (Fin 4)) := {⟨{0}, {1}⟩, ⟨{2}, {3}⟩}

/-- The tuple with values `a, b, c, d`. -/
def tup4 (a b c d : ℕ) : Tuple (Fin 4) ℕ := ![some a, some b, some c, some d]

/-- A relation over `ABCD` satisfying `G`. -/
def u : Finset (Tuple (Fin 4) ℕ) := {tup4 1 1 1 1, tup4 2 2 2 2}

theorem u_isOver : IsOver Finset.univ u := by
  unfold IsOver Tuple.IsOver
  decide

theorem u_satisfies : Satisfies (↑u : Set (Tuple (Fin 4) ℕ)) G := by
  simp only [Satisfies, FD.HoldsIn, Finset.mem_coe]
  decide

example : findKey G (List.finRange 4) = {0, 2} := by decide

/-- The dependency schemes `AB` and `CD` alone lose information ... -/
example : joinProjections [{0, 1}, {2, 3}] u ≠ u := by decide

/-- ... and adding the key scheme `AC` makes the decomposition lossless. -/
example : synthesize [⟨{0}, {1}⟩, ⟨{2}, {3}⟩] {0, 2} = [{0, 2}, {0, 1}, {2, 3}] := by decide

example : joinProjections (synthesize [⟨{0}, {1}⟩, ⟨{2}, {3}⟩] {0, 2}) u = u :=
  synthesize_lossless (by decide) (by decide) u_isOver u_satisfies

/-! ### Satisfaction on a sub-schema -/

/-- On the schema `AB`, `{C → A}` imposes nothing, so the decomposition of `AB` into `A` and `B`
is lossy: the relation `{(1, 1), (2, 2)}` over `AB` is not the join of its projections. -/
example : ¬ LosslessJoin ℕ ({⟨{2}, {0}⟩} : Finset (FD (Fin 3))) {0} {1} := by
  intro h
  have hr : IsOver ({0} ∪ {1}) ({![some 1, some 1, none], ![some 2, some 2, none]} :
      Finset (Tuple (Fin 3) ℕ)) := by
    unfold IsOver Tuple.IsOver
    decide
  have := h _ hr (by decide)
  revert this
  decide

end Cslib.Databases.NormalFormsTests
