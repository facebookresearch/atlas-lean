/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplex

/-!
# Canonical filtered colimit of finite subcomplexes

Every simplicial set in an arbitrary value universe is the filtered union
of its finite subcomplexes. The existing subtype index, inclusion diagram,
cocone and colimit universal property retain their original names. A finite
set of simplices from arbitrary degrees lies in a single finite subcomplex.

Finiteness counts nondegenerate simplices. The index lives in the value
universe and uses native smallness; no separate index or size assumption is
needed. This is the finite simplicial specialization of Cisinski 2006,
Propositions 1.2.15 and 1.2.16. The original universe-zero realization clients
remain specializations of this API.
-/

@[expose] public section

open CategoryTheory Limits SSet Simplicial

universe u

namespace SSet.Subcomplex

variable (Y : SSet.{u})

/-- Finite subcomplexes of `Y`, ordered by inclusion. -/
abbrev FiniteSubcomplexIndex :=
  {S : Y.Subcomplex // SSet.Finite (S : SSet.{u})}

/-- The empty subcomplex, viewed in `SSet`, is finite. -/
private instance finite_bot :
    SSet.Finite ((⊥ : Y.Subcomplex) : SSet.{u}) := by
  have hbot : SSet.Finite (⊥_ SSet.{u}) := inferInstance
  exact @SSet.finite_of_iso _ _
    (IsInitial.uniqueUpToIso (isInitialBot (X := Y))
      (initialIsInitial (C := SSet.{u}))).symm hbot

/-- Binary suprema of finite subcomplexes are finite, via `SSet.finite_iSup_iff`. -/
private lemma finite_sup (S T : Y.Subcomplex)
    (hS : SSet.Finite (S : SSet.{u})) (hT : SSet.Finite (T : SSet.{u})) :
    SSet.Finite ((S ⊔ T : Y.Subcomplex) : SSet.{u}) := by
  let A : Fin 2 → Y.Subcomplex := ![S, T]
  have hST : (S ⊔ T : Y.Subcomplex) = ⨆ i, A i := by
    apply le_antisymm
    · exact sup_le (le_iSup A 0) (le_iSup A 1)
    · apply iSup_le
      intro i
      fin_cases i <;> simp [A]
  have hfin : SSet.Finite ((⨆ i, A i : Y.Subcomplex) : SSet.{u}) := by
    rw [SSet.finite_iSup_iff]
    intro i
    fin_cases i
    · simpa [A] using hS
    · simpa [A] using hT
  rwa [← hST] at hfin

instance : Nonempty (FiniteSubcomplexIndex Y) :=
  ⟨⟨⊥, finite_bot Y⟩⟩

instance : IsDirectedOrder (FiniteSubcomplexIndex Y) where
  directed a b :=
    ⟨⟨a.val ⊔ b.val, finite_sup Y a.val b.val a.property b.property⟩,
      (show a.val ≤ a.val ⊔ b.val from le_sup_left),
      (show b.val ≤ a.val ⊔ b.val from le_sup_right)⟩

/-- Supremum of all finite subcomplexes is `⊤`. -/
lemma iSup_finiteSubcomplex_eq_top :
    ⨆ (S : FiniteSubcomplexIndex Y), (S.val : Y.Subcomplex) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← iSup_ofSimplex_nonDegenerate_eq_top Y]
  apply iSup_le
  rintro ⟨p, x, hx⟩
  have hfin := finite_ofSimplex Y x
  calc ofSimplex x ≤ (⟨ofSimplex x, hfin⟩ : FiniteSubcomplexIndex Y).val := le_rfl
    _ ≤ ⨆ (S : FiniteSubcomplexIndex Y), (S.val : Y.Subcomplex) :=
        le_iSup _ (⟨ofSimplex x, hfin⟩ : FiniteSubcomplexIndex Y)

/-- A finite set of simplices, in arbitrary degrees, is contained in one
finite subcomplex. The empty set is included. -/
theorem exists_finite_subcomplex_containing (T : Set (Σ n : ℕ, Y _⦋n⦌))
    [Finite T] :
    ∃ V : Y.Subcomplex, SSet.Finite (V : SSet.{u}) ∧
      ∀ s : T, s.val.2 ∈ V.obj (Opposite.op ⦋s.val.1⦌) := by
  let V : Y.Subcomplex := ⨆ s : T, ofSimplex s.val.2
  refine ⟨V, finite_iSup_ofSimplex Y (fun s : T => s.val), ?_⟩
  intro s
  exact (le_iSup (fun t : T => ofSimplex t.val.2) s) _
    (mem_ofSimplex_obj s.val.2)

/-- Underlying monotone family of finite subcomplexes. -/
noncomputable def finiteSubcomplexFamily :
    FiniteSubcomplexIndex Y ⥤ Y.Subcomplex :=
  Monotone.functor (show Monotone (Subtype.val : FiniteSubcomplexIndex Y → Y.Subcomplex)
    from fun _ _ h => h)

/-- Diagram of finite subcomplexes in `SSet.{u}`. -/
noncomputable def finiteSubcomplexDiagram :
    FiniteSubcomplexIndex Y ⥤ SSet.{u} :=
  finiteSubcomplexFamily Y ⋙ toSSetFunctor

/-- Cocone with apex `Y` via `⊤` and `topIso`. -/
noncomputable def finiteSubcomplexCocone :
    Cocone (finiteSubcomplexDiagram Y) where
  pt := Y
  ι :=
    { app S := homOfLE (show S.val ≤ ⊤ from le_top) ≫ (topIso Y).hom
      naturality := fun S T f => by
        dsimp [finiteSubcomplexDiagram, finiteSubcomplexFamily,
          Monotone.functor, toSSetFunctor]
        simp }

/-- `Y` is the colimit of its finite subcomplexes in `SSet.{u}`. -/
noncomputable def isColimit_finiteSubcomplex :
    IsColimit (finiteSubcomplexCocone Y) := by
  have hLUB : IsLUB (Set.range (finiteSubcomplexFamily Y).obj) (⊤ : Y.Subcomplex) := by
    have hsup : ⨆ (S : FiniteSubcomplexIndex Y), (finiteSubcomplexFamily Y).obj S = ⊤ := by
      simpa [finiteSubcomplexFamily] using iSup_finiteSubcomplex_eq_top Y
    rw [← hsup]
    exact isLUB_iSup
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB _ hLUB).isColimit)
    (Cocone.ext (topIso Y))

end SSet.Subcomplex
