/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.ExistsEqProd

@[expose] public section

open MeasureTheory

universe u v

/-- Exact-source consumer, with the original binders and explicit universes. -/
private theorem exactSource
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    {Y : Type v} [MeasurableSpace Y] (ρ : MeasureTheory.Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∃ B : ℕ → Set Y, (∀ n, MeasurableSet (B n)) ∧ (⋃ n, B n) = Set.univ ∧
      ∀ n (K : Set G), IsCompact K → ρ (K ×ˢ B n) < ⊤) :
    ∃ σ : MeasureTheory.Measure Y, MeasureTheory.SigmaFinite σ ∧ ρ = μ.prod σ :=
  MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left μ ρ hinv hfin

/-- Boundary: translation invariance is not automatic. The Dirac measure at
`(0, ())` on `ℤ × Unit` moves under translation by `1` in the first
coordinate, so the invariance hypothesis cannot be dropped. -/
example :
    (MeasureTheory.Measure.dirac ((0 : ℤ), ())).map
        (fun p : ℤ × Unit => (1 + p.1, p.2)) ≠
      MeasureTheory.Measure.dirac ((0 : ℤ), ()) := by
  rw [MeasureTheory.Measure.map_dirac ((0 : ℤ), ())]
  intro h
  have h' := congrArg (fun ν : MeasureTheory.Measure (ℤ × Unit) => ν {((0 : ℤ), ())}) h
  simp at h'
