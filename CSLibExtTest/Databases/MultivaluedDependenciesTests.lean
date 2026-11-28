/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.MultivaluedDependencies
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for multivalued and join dependencies

Attributes `A, B, C = 0, 1, 2`, values natural numbers.
* Boundary: in the course–teacher–book relation `ctb`, `A ↠ B` (and its complement `A ↠ C`)
  holds but `A → B` does not; the decomposition into `AB` and `AC` reconstructs `ctb`.
* Dropping two of its tuples breaks `A ↠ B`, and the decomposition becomes lossy.
* A relation satisfying `A → B` satisfies `A ↠ B` (rule FMVD1).
* Proposition 8.3.3 of Abiteboul–Hull–Vianu for `{A → B}`: `{AB, AC}` gives an implied
  multivalued dependency, `{AB, BC}` does not.
* A three-scheme join dependency that holds, and fails after removing one tuple.
* Fourth normal form, clause by clause: for the Studios dependencies clause (a) holds (the full
  cube refutes every nontrivial functional dependency) but clause (b) fails; project-join normal
  form holds for a key-only schema and fails for Studios; a two-attribute schema with a single
  functional dependency is in fourth normal form (the covering multivalued dependency is trivial);
  a functional dependency mentioning an outside attribute does not constrain a smaller schema.
-/

@[expose] public section

namespace Cslib.Databases.MultivaluedDependenciesTests

open Cslib.Databases

/-- The closure of `X` is contained in every set that contains `X` and is closed under `F`. -/
private theorem attrClosure_subset_of_closed {A : Type*} [Fintype A] [DecidableEq A]
    {F : Finset (FD A)} {X C : Finset A} (hX : X ⊆ C)
    (hC : ∀ g ∈ F, g.lhs ⊆ C → g.rhs ⊆ C) : attrClosure F X ⊆ C := by
  let t₀ : A → Bool := fun _ => true
  let t₁ : A → Bool := fun a => decide (a ∈ C)
  have hr : Satisfies ({t₀, t₁} : Set (A → Bool)) F := by
    have key : ∀ g ∈ F, (∀ a ∈ g.lhs, t₀ a = t₁ a) → ∀ a ∈ g.rhs, t₀ a = t₁ a :=
      fun g hg hl a ha => by
        have : g.lhs ⊆ C := fun b hb => by simpa [t₀, t₁] using hl b hb
        simpa [t₀, t₁] using hC g hg this ha
    intro g hg t ht u hu hagree
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · exact fun _ _ => rfl
    · exact key g hg hagree
    · exact fun a ha => (key g hg (fun b hb => (hagree b hb).symm) a ha).symm
    · exact fun _ _ => rfl
  intro a ha
  have := (derives_attrClosure F X).sound hr t₀ (by simp) t₁ (by simp)
    (fun b hb => by simpa [t₀, t₁] using hX hb) a ha
  simpa [t₀, t₁] using this

/-- The tuple with values `a`, `b`, `c` on `A`, `B`, `C`. -/
def tup (a b c : ℕ) : Tuple (Fin 3) ℕ := ![some a, some b, some c]

/-- Course `A`, teacher `B`, book `C`: course 1 has teachers 1, 2 and books 1, 2, in every
combination. -/
def ctb : Finset (Tuple (Fin 3) ℕ) := {tup 1 1 1, tup 1 1 2, tup 1 2 1, tup 1 2 2}

theorem ctb_isOver : IsOver Finset.univ ctb := by
  unfold IsOver Tuple.IsOver
  decide

-- The boundary: `A ↠ B` holds in `ctb`, but `A → B` does not.
example : MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ ctb ∧
    ¬ FD.HoldsIn ⟨{0}, {1}⟩ (↑ctb : Set (Tuple (Fin 3) ℕ)) := by
  refine ⟨by decide, ?_⟩
  simp only [FD.HoldsIn, Finset.mem_coe]
  decide

-- Complementation: `A ↠ C` holds as well, directly and by `MVD.holdsIn_compl`.
example : MVD.HoldsIn Finset.univ ⟨{0}, {2}⟩ ctb := by decide

example : MVD.HoldsIn Finset.univ ⟨{0}, Finset.univ \ {1}⟩ ctb :=
  (MVD.holdsIn_compl (Finset.subset_univ _)).mp (by decide)

-- The exchange witness for `tup 1 1 1` and `tup 1 2 2` is `tup 1 1 2`.
example : ∃ w ∈ ctb, (∀ a ∈ ({0} ∪ {1} : Finset (Fin 3)), w a = tup 1 1 1 a) ∧
    ∀ a ∈ (Finset.univ \ {1} : Finset (Fin 3)), w a = tup 1 2 2 a :=
  (MVD.holdsIn_iff_exchange ctb_isOver (Finset.subset_univ _) (Finset.subset_univ _)).mp
    (by decide) _ (by decide) _ (by decide) (by decide)

-- `{AB, AC}` reconstructs `ctb`, through the binary criterion.
example : join (project {0, 1} ctb) (project {0, 2} ctb) = ctb :=
  join_project_eq_iff_mvd.mpr (by decide)

/-- Two of the four tuples of `ctb`. -/
def ctb₂ : Finset (Tuple (Fin 3) ℕ) := {tup 1 1 1, tup 1 2 2}

-- Without the other two tuples, `A ↠ B` fails and the decomposition is lossy.
example : ¬ MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ ctb₂ ∧
    join (project {0, 1} ctb₂) (project {0, 2} ctb₂) ≠ ctb₂ := by
  decide

private theorem ctb₂_isOver : IsOver Finset.univ ctb₂ := by
  unfold IsOver Tuple.IsOver
  decide

/-- A relation over `ABC` satisfying `A → B`. -/
def s : Finset (Tuple (Fin 3) ℕ) := {tup 1 2 3, tup 1 2 4, tup 2 5 3}

theorem s_isOver : IsOver Finset.univ s := by
  unfold IsOver Tuple.IsOver
  decide

example : MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ s :=
  MVD.holdsIn_of_holdsIn_fd s_isOver (Finset.subset_univ _) (Finset.subset_univ _)
    (by simp only [FD.HoldsIn, Finset.mem_coe]; decide)

/-- `A → B`. -/
def FAB : Finset (FD (Fin 3)) := {⟨{0}, {1}⟩}

-- Proposition 8.3.3: `{A → B}` implies `A ↠ B` on `ABC` (`AB ∩ AC = A`) ...
example : ∀ r : Finset (Tuple (Fin 3) ℕ), IsOver ({0, 1} ∪ {0, 2}) r →
    SatisfiesOn FAB ({0, 1} ∪ {0, 2}) r →
      MVD.HoldsIn ({0, 1} ∪ {0, 2}) ⟨{0, 1} ∩ {0, 2}, {0, 1}⟩ r :=
  (losslessJoin_iff_mvd.symm.trans
    (losslessJoin_iff (show (0 : ℕ) ≠ 1 by decide) (by decide))).mpr (Or.inl (by decide))

-- ... but not `B ↠ A` (`AB ∩ BC = B`).
example : ¬ ∀ r : Finset (Tuple (Fin 3) ℕ), IsOver ({0, 1} ∪ {1, 2}) r →
    SatisfiesOn FAB ({0, 1} ∪ {1, 2}) r →
      MVD.HoldsIn ({0, 1} ∪ {1, 2}) ⟨{0, 1} ∩ {1, 2}, {0, 1}⟩ r := by
  intro h
  have := (losslessJoin_iff_mvd.symm.trans
    (losslessJoin_iff (show (0 : ℕ) ≠ 1 by decide) (by decide))).mp h
  revert this
  decide

/-- The join dependency `⋈[AB, BC, AC]`. -/
def jd3 : JD (Fin 3) := ⟨[{0, 1}, {1, 2}, {0, 2}]⟩

-- It holds in this relation, and fails once `tup 1 1 1` is removed, although that tuple is
-- still in the join of the projections.
example : jd3.HoldsIn ({tup 1 1 2, tup 1 2 1, tup 2 1 1, tup 1 1 1} : Finset (Tuple (Fin 3) ℕ)) ∧
    ¬ jd3.HoldsIn ({tup 1 1 2, tup 1 2 1, tup 2 1 1} : Finset (Tuple (Fin 3) ℕ)) := by
  decide

/-- `Studios` (Abiteboul–Hull–Vianu, Example 11.2.15): the single multivalued dependency
`A ↠ B` over `ABC`. -/
def Jstudio : Finset (JD (Fin 3)) := {MVD.toJD Finset.univ ⟨{0}, {1}⟩}

/-- The full cube `{0, 1}³`: the eight tuples with entries in `{0, 1}`. -/
private def cube : Finset (Tuple (Fin 3) ℕ) :=
  {tup 0 0 0, tup 0 0 1, tup 0 1 0, tup 0 1 1, tup 1 0 0, tup 1 0 1, tup 1 1 0, tup 1 1 1}

private theorem cube_isOver : IsOver Finset.univ cube := by
  unfold IsOver Tuple.IsOver
  decide

private theorem cube_satisfiesOn : SatisfiesOn (∅ : Finset (FD (Fin 3))) Finset.univ cube := by
  decide

private theorem cube_mvd_premise : ∀ j ∈ Jstudio, j.HoldsIn cube := by
  intro j hj
  simp only [Jstudio, Finset.mem_singleton] at hj
  subst hj
  decide

/-- Two cube tuples differing only at `a` refute any functional dependency `X → Y` with
`a ∈ Y` and `a ∉ X` that holds in the cube. -/
private theorem cube_refutes {X Y : Finset (Fin 3)} {a : Fin 3} (haY : a ∈ Y) (haX : a ∉ X)
    (h : FD.HoldsIn ⟨X, Y⟩ (↑cube : Set (Tuple (Fin 3) ℕ))) : False := by
  have h3 : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  simp only [FD.HoldsIn, Finset.mem_coe] at h
  rcases h3 a with rfl | rfl | rfl
  · have h0 : ∀ b : Fin 3, b ≠ 0 → tup 0 0 0 b = tup 1 0 0 b := by decide
    have hne : tup 0 0 0 0 ≠ tup 1 0 0 0 := by decide
    exact hne (h (tup 0 0 0) (by decide) (tup 1 0 0) (by decide)
      (fun b hb => h0 b (fun e => haX (e ▸ hb))) 0 haY)
  · have h1 : ∀ b : Fin 3, b ≠ 1 → tup 0 0 0 b = tup 0 1 0 b := by decide
    have hne : tup 0 0 0 1 ≠ tup 0 1 0 1 := by decide
    exact hne (h (tup 0 0 0) (by decide) (tup 0 1 0) (by decide)
      (fun b hb => h1 b (fun e => haX (e ▸ hb))) 1 haY)
  · have h2 : ∀ b : Fin 3, b ≠ 2 → tup 0 0 0 b = tup 0 0 1 b := by decide
    have hne : tup 0 0 0 2 ≠ tup 0 0 1 2 := by decide
    exact hne (h (tup 0 0 0) (by decide) (tup 0 0 1) (by decide)
      (fun b hb => h2 b (fun e => haX (e ▸ hb))) 2 haY)

-- Studios under one set of premises (no FDs, the single MVD `A ↠ B`): clause (a) of fourth
-- normal form holds, because the full cube satisfies the MVD and refutes every nontrivial FD,
-- but the schema is not in fourth normal form, since clause (b) fails on `ctb`.
example : (∀ X ⊆ (Finset.univ : Finset (Fin 3)), ∀ Y ⊆ Finset.univ, ¬ Y ⊆ X →
ImpliesFD ℕ Finset.univ ∅ Jstudio ⟨X, Y⟩ →
ImpliesFD ℕ Finset.univ ∅ Jstudio ⟨X, Finset.univ⟩) ∧
¬ IsFourthNF ℕ Finset.univ ∅ Jstudio := by
  constructor
  · intro X hX Y hY hYX hImp
    obtain ⟨a, haY, haX⟩ := Finset.not_subset.mp hYX
    exact False.elim
      (cube_refutes haY haX (hImp cube cube_isOver cube_satisfiesOn cube_mvd_premise))
  · intro h
    have hFD := h.2.2 {0} (Finset.subset_univ _) {1} (Finset.subset_univ _) (by decide)
      (by decide) (fun _ _ _ hJ => hJ _ (Finset.mem_singleton_self _)) ctb ctb_isOver
      (by decide) (by decide)
    revert hFD
    simp only [FD.HoldsIn, Finset.mem_coe]
    decide

example : IsPJNF ℕ (Finset.univ : Finset (Fin 3)) {⟨{0}, Finset.univ⟩} ∅ := by
  constructor
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · intro j hcover hjimp r hr hkey
    have hF : SatisfiesOn ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3))) Finset.univ r := by
      intro X hX Y hY hD
      have hYcl : Y ⊆ attrClosure ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3))) X :=
        derives_iff_subset_attrClosure.mp hD
      by_cases h0X : (0 : Fin 3) ∈ X
      · have hDer : Derives ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3)))
            ⟨X, Finset.univ⟩ := by
          rw [derives_iff_subset_attrClosure]
          have hg : (⟨{0}, Finset.univ⟩ : FD (Fin 3)) ∈
              ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3))) :=
            Finset.mem_singleton_self _
          have hlhs : (⟨{0}, Finset.univ⟩ : FD (Fin 3)).lhs ⊆
              attrClosure ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3))) X := by
            intro b hb
            dsimp only at hb
            rw [Finset.mem_singleton.mp hb]
            exact subset_attrClosure _ _ h0X
          exact rhs_subset_attrClosure hg hlhs
        have hImp : ImpliesFD ℕ Finset.univ ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3)))
            ∅ ⟨X, Finset.univ⟩ := by
          intro r' hr' hF' _
          exact hF' X hX Finset.univ (Finset.subset_univ _) hDer
        have hKey := hkey X hX hImp
        simp only [FD.HoldsIn, Finset.mem_coe] at hKey ⊢
        intro t ht u hu hagree a ha
        exact hKey t ht u hu hagree a (hY ha)
      · have hclosed : attrClosure ({⟨{0}, Finset.univ⟩} : Finset (FD (Fin 3))) X ⊆ X := by
          refine attrClosure_subset_of_closed subset_rfl fun g hg hlhs => ?_
          simp only [Finset.mem_singleton] at hg
          subst hg
          dsimp only at hlhs
          exact absurd (hlhs (Finset.mem_singleton_self 0)) h0X
        have hYX : Y ⊆ X := hYcl.trans hclosed
        simp only [FD.HoldsIn, Finset.mem_coe]
        intro t ht u hu hagree a ha
        exact hagree a (hYX ha)
    exact hjimp r hr hF (fun j' hj' => absurd hj' (Finset.notMem_empty j'))

example : ¬ IsPJNF ℕ (Finset.univ : Finset (Fin 3)) ∅ Jstudio := by
  intro h
  have hcover : (MVD.toJD (Finset.univ : Finset (Fin 3)) ⟨{0}, {1}⟩).IsOver Finset.univ :=
    MVD.toJD_isOver (Finset.subset_univ _) (Finset.subset_univ _)
  have hjimp : ImpliesJD ℕ Finset.univ ∅ Jstudio (MVD.toJD Finset.univ ⟨{0}, {1}⟩) :=
    fun _ _ _ hJ => hJ _ (Finset.mem_singleton_self _)
  have hkeys : ∀ X ⊆ Finset.univ,
      ImpliesFD ℕ Finset.univ ∅ Jstudio ⟨X, Finset.univ⟩ →
      FD.HoldsIn ⟨X, Finset.univ⟩ (↑ctb₂ : Set (Tuple (Fin 3) ℕ)) := by
    intro X hX hK
    by_cases hXU : X = Finset.univ
    · subst hXU
      intro t ht u hu hagree a ha
      exact hagree a ha
    · have hex : ∃ a : Fin 3, a ∉ X := by
        by_contra hc
        rw [not_exists] at hc
        exact hXU (Finset.eq_univ_of_forall fun a => of_not_not (hc a))
      obtain ⟨a, haX⟩ := hex
      exact False.elim
        (cube_refutes (Finset.mem_univ a) haX
          (hK cube cube_isOver cube_satisfiesOn cube_mvd_premise))
  have hM := h.2 _ hcover hjimp ctb₂ ctb₂_isOver hkeys
  have hno : ¬ MVD.HoldsIn Finset.univ ⟨{0}, {1}⟩ ctb₂ := by decide
  exact hno hM

/-- The tuple with values `a`, `b` on `0`, `1`. -/
private def tup2 (a b : ℕ) : Tuple (Fin 2) ℕ := ![some a, some b]

/-- Two diagonal tuples. -/
private def diag : Finset (Tuple (Fin 2) ℕ) := {tup2 0 0, tup2 1 1}

/-- Two tuples agreeing on `1`. -/
private def agree1 : Finset (Tuple (Fin 2) ℕ) := {tup2 0 0, tup2 1 0}

private theorem diag_isOver : IsOver Finset.univ diag := by
  unfold IsOver Tuple.IsOver
  decide

private theorem agree1_isOver : IsOver Finset.univ agree1 := by
  unfold IsOver Tuple.IsOver
  decide

private theorem diag_sat :
    SatisfiesOn ({⟨{0}, {1}⟩} : Finset (FD (Fin 2))) Finset.univ diag := by
  decide

private theorem agree1_sat :
    SatisfiesOn ({⟨{0}, {1}⟩} : Finset (FD (Fin 2))) Finset.univ agree1 := by
  decide

private theorem fin2_cases : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide

private theorem fin2_powerset :
    (Finset.univ : Finset (Fin 2)).powerset = {∅, {0}, {1}, {0, 1}} := by decide

example : IsFourthNF ℕ (Finset.univ : Finset (Fin 2)) {⟨{0}, {1}⟩} ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · intro X hX Y hY hYX hImp
    by_cases h0X : (0 : Fin 2) ∈ X
    · have hDer : Derives ({⟨{0}, {1}⟩} : Finset (FD (Fin 2))) ⟨X, Finset.univ⟩ := by
        rw [derives_iff_subset_attrClosure]
        intro a _
        rcases fin2_cases a with rfl | rfl
        · exact subset_attrClosure _ _ h0X
        · have hg : (⟨{0}, {1}⟩ : FD (Fin 2)) ∈ ({⟨{0}, {1}⟩} : Finset (FD (Fin 2))) :=
            Finset.mem_singleton_self _
          have hlhs : (⟨{0}, {1}⟩ : FD (Fin 2)).lhs ⊆
              attrClosure ({⟨{0}, {1}⟩} : Finset (FD (Fin 2))) X := by
            intro b hb
            dsimp only at hb
            rw [Finset.mem_singleton.mp hb]
            exact subset_attrClosure _ _ h0X
          exact rhs_subset_attrClosure hg hlhs (Finset.mem_singleton_self 1)
      intro r hr hF _
      exact hF X hX Finset.univ (Finset.subset_univ _) hDer
    · obtain ⟨a, haY, haX⟩ := Finset.not_subset.mp hYX
      exfalso
      have hXp : X ∈ (Finset.univ : Finset (Fin 2)).powerset := Finset.mem_powerset.mpr hX
      rw [fin2_powerset] at hXp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXp
      rcases hXp with rfl | rfl | rfl | rfl
      · rcases fin2_cases a with rfl | rfl
        · have hFD := hImp diag diag_isOver diag_sat
            (fun j hj => absurd hj (Finset.notMem_empty j))
          simp only [FD.HoldsIn, Finset.mem_coe] at hFD
          have hne : tup2 0 0 0 ≠ tup2 1 1 0 := by decide
          exact hne (hFD (tup2 0 0) (by decide) (tup2 1 1) (by decide)
            (fun b hb => absurd hb (Finset.notMem_empty b)) 0 haY)
        · have hFD := hImp diag diag_isOver diag_sat
            (fun j hj => absurd hj (Finset.notMem_empty j))
          simp only [FD.HoldsIn, Finset.mem_coe] at hFD
          have hne : tup2 0 0 1 ≠ tup2 1 1 1 := by decide
          exact hne (hFD (tup2 0 0) (by decide) (tup2 1 1) (by decide)
            (fun b hb => absurd hb (Finset.notMem_empty b)) 1 haY)
      · exact h0X (by decide)
      · rcases fin2_cases a with rfl | rfl
        · have hFD := hImp agree1 agree1_isOver agree1_sat
            (fun j hj => absurd hj (Finset.notMem_empty j))
          simp only [FD.HoldsIn, Finset.mem_coe] at hFD
          have hne : tup2 0 0 0 ≠ tup2 1 0 0 := by decide
          exact hne (hFD (tup2 0 0) (by decide) (tup2 1 0) (by decide)
            (by decide) 0 haY)
        · exact haX (by decide)
      · exact h0X (by decide)
  · intro X hX Y hY hYX hne hJD
    have hXp : X ∈ (Finset.univ : Finset (Fin 2)).powerset := Finset.mem_powerset.mpr hX
    have hYp : Y ∈ (Finset.univ : Finset (Fin 2)).powerset := Finset.mem_powerset.mpr hY
    rw [fin2_powerset] at hXp hYp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXp hYp
    rcases hXp with rfl | rfl | rfl | rfl <;> rcases hYp with rfl | rfl | rfl | rfl
    all_goals exfalso
    all_goals (first | exact hYX (by decide) | exact hne (by decide) | (have hM := hJD diag diag_isOver diag_sat (fun j hj => absurd hj (Finset.notMem_empty j)); revert hM; decide))

/-- The tuple with values `a`, `b`, `c` on `0`, `1`, `2` and no value on `3`. -/
private def tup4 (a b c : ℕ) : Tuple (Fin 4) ℕ := ![some a, some b, some c, none]

/-- Two tuples over `{0, 1, 2}` agreeing on `{0}` and differing on `2`. -/
private def reg : Finset (Tuple (Fin 4) ℕ) := {tup4 0 0 0, tup4 0 0 1}

private theorem reg_isOver : IsOver {0, 1, 2} reg := by
  unfold IsOver Tuple.IsOver
  decide

private theorem reg_sat : SatisfiesOn
    ({⟨{0}, {1}⟩, ⟨{3}, {0, 1, 2}⟩} : Finset (FD (Fin 4))) {0, 1, 2} reg := by
  decide

example : ¬ IsFourthNF ℕ {0, 1, 2}
    ({⟨{0}, {1}⟩, ⟨{3}, {0, 1, 2}⟩} : Finset (FD (Fin 4))) ∅ := by
  intro h
  have hImp1 : ImpliesFD ℕ {0, 1, 2}
      ({⟨{0}, {1}⟩, ⟨{3}, {0, 1, 2}⟩} : Finset (FD (Fin 4))) ∅ ⟨{0}, {1}⟩ := by
    intro r hr hF _
    exact hF {0} (by decide) {1} (by decide) (by decide)
  have hImpU := h.2.1 {0} (by decide) {1} (by decide) (by decide) hImp1
  have hFD := hImpU reg reg_isOver reg_sat (fun j hj => absurd hj (Finset.notMem_empty j))
  simp only [FD.HoldsIn, Finset.mem_coe] at hFD
  have hne : tup4 0 0 0 2 ≠ tup4 0 0 1 2 := by decide
  exact hne (hFD (tup4 0 0 0) (by decide) (tup4 0 0 1) (by decide) (by decide) 2 (by decide))

end Cslib.Databases.MultivaluedDependenciesTests
