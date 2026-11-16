/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/Stabilization.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.Free
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.StructureMap

/-!
# Stabilization maps between free symmetric spectra

The canonical map `F_(1+n)(S¹ ∧ K) → F_n K` extends the suspension of the universal
generator of `F_n K` by its structure map. These maps are natural in `K`. They are the
maps inverted when passing from the level theory of symmetric spectra to the stable theory.

Under the free/evaluation and suspension/loop adjunctions, precomposition with this map
is postcomposition with the adjoint structure map `E_n → Ω E_(1+n)`. We prove this on
actual maps, together with its strict bijectivity criterion. In particular, testing against
all pointed simplicial sets detects when the adjoint structure map is an isomorphism.
This is a point-set statement, not a claim that strict bijectivity detects Ω-spectra:
stable localization instead uses derived mapping spaces and weak equivalences.

The construction uses the existing `SymmetricSpectrum.freeEvaluationAdjunction` and
`CategoryTheory.Mod.smashPowStructureMap`, retaining the left suspension coordinate
and the symmetric actions carried by the sphere modules.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 3.1 and 3.4 (free spectra and the maps used for stabilization).
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource.SymmetricSpectrum

/-- The canonical stabilization map `F_(1+n)(S¹ ∧ K) ⟶ F_n K`, adjoint to the
suspension of the universal generator followed by the structure map of `F_n K`. -/
noncomputable def freeStabilizationMap (n : ℕ) (K : PointedSSet.{0}) :
    (free (1 + n)).obj (PointedSSet.circle ⊗ K) ⟶ (free n).obj K :=
  freeDesc _ (PointedSSet.circle ◁ freeι n K ≫ ((free n).obj K).smashPowStructureMap n)

/-- On its generating level the stabilization map is the structure map applied to
the suspended generator. -/
@[simp, reassoc]
lemma freeι_stabilizationMap (n : ℕ) (K : PointedSSet.{0}) :
    freeι (1 + n) (PointedSSet.circle ⊗ K) ≫
        (evaluation (1 + n)).map (freeStabilizationMap n K) =
      PointedSSet.circle ◁ freeι n K ≫ ((free n).obj K).smashPowStructureMap n := by
  simp [freeStabilizationMap]

/-- Precomposition with stabilization extends a suspended level map by the target's
structure map. -/
@[simp, reassoc]
lemma freeStabilizationMap_comp_freeDesc (n : ℕ) {K : PointedSSet.{0}}
    (E : SymmetricSpectrum) (f : K ⟶ (evaluation n).obj E) :
    freeStabilizationMap n K ≫ freeDesc E f =
      freeDesc E (PointedSSet.circle ◁ f ≫ E.smashPowStructureMap n) := by
  rw [freeStabilizationMap, freeDesc_comp]
  congr 1
  rw [Category.assoc, Mod.smashPowStructureMap_hom, ← whiskerLeft_comp_assoc, freeι_desc]

/-- The stabilization maps are natural in the pointed simplicial set of generators. -/
@[reassoc]
lemma freeStabilizationMap_naturality (n : ℕ) {K L : PointedSSet.{0}} (f : K ⟶ L) :
    (free (1 + n)).map (PointedSSet.circle ◁ f) ≫ freeStabilizationMap n L =
      freeStabilizationMap n K ≫ (free n).map f := by
  rw [freeStabilizationMap, freeStabilizationMap, freeDesc_comp]
  calc
    _ = freeDesc _ (PointedSSet.circle ◁ f ≫
        (PointedSSet.circle ◁ freeι n L ≫ ((free n).obj L).smashPowStructureMap n)) :=
      free_map_freeDesc _ _ _
    _ = _ := by
      congr 1
      rw [Category.assoc, Mod.smashPowStructureMap_hom, ← whiskerLeft_comp_assoc,
        ← whiskerLeft_comp_assoc, freeι_naturality]

/-- Stabilization as a natural transformation `F_(1+n) Σ ⟶ F_n`. -/
noncomputable def freeStabilization (n : ℕ) :
    PointedSSet.suspension ⋙ free (1 + n) ⟶ free n where
  app K := freeStabilizationMap n K
  naturality _ _ f := freeStabilizationMap_naturality n f

/-- The components of the stabilization transformation are the canonical free maps. -/
@[simp]
lemma freeStabilization_app (n : ℕ) (K : PointedSSet.{0}) :
    (freeStabilization n).app K = freeStabilizationMap n K := (rfl)

/-- Under free/evaluation, restriction along stabilization applies the target structure
map to the suspension of the restriction to the original generator. -/
lemma freeEvaluationAdjunction_homEquiv_stabilization (n : ℕ) {K : PointedSSet.{0}}
    {E : SymmetricSpectrum} (f : (free n).obj K ⟶ E) :
    (freeEvaluationAdjunction (1 + n)).homEquiv _ E (freeStabilizationMap n K ≫ f) =
      PointedSSet.circle ◁ ((freeEvaluationAdjunction n).homEquiv K E f) ≫
        E.smashPowStructureMap n := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    (evaluation (1 + n)).map_comp, freeEvaluationAdjunction_unit_app,
    freeEvaluationAdjunction_unit_app, freeι_stabilizationMap_assoc]
  simp [Mod.smashPowStructureMap_hom, whiskerLeft_comp]

/-- Under free/evaluation and suspension/loop, restriction along stabilization is
postcomposition with the adjoint structure map. -/
lemma curry_freeEvaluationAdjunction_homEquiv_stabilization (n : ℕ)
    {K : PointedSSet.{0}} {E : SymmetricSpectrum} (f : (free n).obj K ⟶ E) :
    MonoidalClosed.curry
        ((freeEvaluationAdjunction (1 + n)).homEquiv _ E (freeStabilizationMap n K ≫ f)) =
      (freeEvaluationAdjunction n).homEquiv K E f ≫ E.smashPowAdjointStructureMap n := by
  rw [freeEvaluationAdjunction_homEquiv_stabilization, MonoidalClosed.curry_natural_left,
    Mod.smashPowAdjointStructureMap_def]

/-- Restriction along stabilization is bijective precisely when postcomposition with
the adjoint structure map is bijective on maps out of the same pointed simplicial set.
No fibrancy or weak-equivalence hypothesis enters this strict statement. -/
theorem bijective_freeStabilizationMap_precomp_iff (n : ℕ) (K : PointedSSet.{0})
    (E : SymmetricSpectrum) :
    Function.Bijective (fun f : (free n).obj K ⟶ E ↦ freeStabilizationMap n K ≫ f) ↔
      Function.Bijective (fun f : K ⟶ (evaluation n).obj E ↦
        f ≫ E.smashPowAdjointStructureMap n) := by
  let e := (freeEvaluationAdjunction n).homEquiv K E
  let e' := ((freeEvaluationAdjunction (1 + n)).homEquiv (PointedSSet.circle ⊗ K) E).trans
    ((ihom.adjunction PointedSSet.circle).homEquiv K ((evaluation (1 + n)).obj E))
  rw [← Equiv.comp_bijective _ e', ← Equiv.bijective_comp e]
  have h : e' ∘ (fun f : (free n).obj K ⟶ E ↦ freeStabilizationMap n K ≫ f) =
      (fun f : K ⟶ (evaluation n).obj E ↦ f ≫ E.smashPowAdjointStructureMap n) ∘ e := by
    funext f
    exact curry_freeEvaluationAdjunction_homEquiv_stabilization n f
  rw [h]

/-- The adjoint structure map in level `n` is an isomorphism exactly when all strict
mapping sets into `E` invert the corresponding free stabilization maps. This is the
strict, underived recognition statement, not the weak-equivalence condition for Ω-spectra. -/
theorem isIso_adjointStructureMap_iff (n : ℕ) (E : SymmetricSpectrum) :
    IsIso (E.smashPowAdjointStructureMap n) ↔
      ∀ K : PointedSSet.{0}, Function.Bijective
        (fun f : (free n).obj K ⟶ E ↦ freeStabilizationMap n K ≫ f) := by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun K ↦ (bijective_freeStabilizationMap_precomp_iff n K E).symm

end MathlibExt.SpectraSource.SymmetricSpectrum
