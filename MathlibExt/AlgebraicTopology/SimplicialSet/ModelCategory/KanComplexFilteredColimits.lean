/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Filtered colimits of Kan complexes

Classical fact: a finite simplicial set is finitely presentable in `SSet`,
so a map from a finite simplicial set into a filtered colimit factors through
some stage, and equalities of such maps are coequalized at a later stage.
Via the horn-filling criterion `SSet.KanComplex.iff` this implies that a
filtered colimit of Kan complexes is again a Kan complex.

Standard source: Goerss–Jardine, *Simplicial Homotopy Theory*, VII Lemma 3.5.
The formal fact used here is `SSet.Finite → IsFinitelyPresentable` from
`Mathlib.AlgebraicTopology.SimplicialSet.Presentable`, so filtered colimits
commute with the finite lifting data `Λ[n,i] ⟶ –` and `Δ[n] ⟶ –`.

This file exposes only the reusable Kan-colimit closure; no other
homotopical structure is claimed here.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

namespace KanComplex

variable {J : Type u} [Category.{u} J] [IsFiltered J]

/-- Filtered colimits of Kan complexes are Kan.

For a finite horn `Λ[n+1,i]` and a compatible family
`f : ∀ j ≠ i, Δ[n] ⟶ colim F`, the universal map
`φ = IsCompatible.desc hf : Λ[n+1,i] ⟶ colim F` factors through some
`F.obj j` because `Λ[n+1,i]` is finite hence finitely presentable
(`SSet.Finite → IsFinitelyPresentable`). The chosen representative
`φ' : Λ[n+1,i] ⟶ F.obj j` admits a Kan filler
`σ : Δ[n+1] ⟶ F.obj j` by `KanComplex.hornFilling`; then
`σ ≫ colimit.ι.app j` fills `f` in the colimit via `horn.ι_ι` and
`IsCompatible.ι_desc`. -/
theorem ofIsFilteredColimit {F : J ⥤ SSet.{u}}
    (hF : ∀ j, KanComplex (F.obj j)) {c : Cocone F} (hc : IsColimit c) :
    KanComplex c.pt := by
  rw [KanComplex.iff]
  intro n i f hf
  let φ : (Λ[n + 1, i] : SSet.{u}) ⟶ c.pt := hf.desc
  have hφ : ∀ (j : Fin (n + 2)) (hj : j ≠ i), SSet.horn.ι i j hj ≫ φ = f j hj :=
    fun j hj => hf.ι_desc j hj
  have : IsFinitelyPresentable.{u} (Λ[n + 1, i] : SSet.{u}) := inferInstance
  obtain ⟨j, φ', hφ'⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit (X := (Λ[n + 1, i] : SSet.{u})) hc φ
  have : KanComplex (F.obj j) := hF j
  obtain ⟨σ, hσ⟩ := SSet.KanComplex.hornFilling (S := F.obj j) φ'
  refine ⟨σ ≫ c.ι.app j, fun j' hj' => ?_⟩
  calc stdSimplex.δ j' ≫ (σ ≫ c.ι.app j)
      = (SSet.horn.ι i j' hj' ≫ Λ[n + 1, i].ι) ≫ σ ≫ c.ι.app j := by
        rw [← SSet.horn.ι_ι]
    _ = SSet.horn.ι i j' hj' ≫ (Λ[n + 1, i].ι ≫ σ) ≫ c.ι.app j := by
        simp only [Category.assoc]
    _ = SSet.horn.ι i j' hj' ≫ φ' ≫ c.ι.app j := by
        rw [← hσ]
    _ = SSet.horn.ι i j' hj' ≫ φ := by
        rw [hφ']
    _ = f j' hj' := by
        rw [← hφ j' hj']

/-- Reusable closure form: the predicate `KanComplex` is stable under filtered
colimits in `SSet`. This is the `Prop`-level form of `ofIsFilteredColimit`
packaged for later KQ3/KQ4 callers. -/
theorem isClosedUnderFilteredColimits :
    ∀ {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ SSet.{u}),
      (∀ j, KanComplex (F.obj j)) → ∀ {c : Cocone F}, IsColimit c → KanComplex c.pt :=
  fun F hF _c hc => ofIsFilteredColimit (J := _) (F := F) hF hc

end KanComplex

end SSet
