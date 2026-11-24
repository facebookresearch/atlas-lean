/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentationHomology
public import MathlibExt.Algebra.Homology.ChainComplexKernelTail
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.DimensionShift
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Computing left-derived functors with acyclic resolutions

An augmented quasi-isomorphism with positive-degree F-acyclic terms computes left derivation for a
right-exact additive functor. The proof passes to the kernel-augmented tail. Degrees zero and one
use the augmentation cokernel and the boundary-as-kernel description; higher degrees use the
generic δ-functor dimension shift and restriction homology.

The construction returns an isomorphism. It requires projective resolution availability and
finite-colimit preservation. It does not require projectivity of the supplied resolution terms or
preservation of homology.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A left-derived object computed from a augmented acyclic complex. -/
noncomputable def leftDerivedObjIsoHomologyOfAcyclicResolution
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {M : C} (Q : ChainComplex C ℕ) (π : Q ⟶ (ChainComplex.single₀ C).obj M)
    [QuasiIso π]
    (hQ : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (Q.X q)))
    (n : ℕ) :
    (F.leftDerived n).obj M ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology n := by
  cases n with
  | zero =>
      exact F.leftDerivedZeroIsoSelf.app M ≪≫
        (ChainComplex.homologyZeroIsoOfPreservedAugmentation F π).symm
  | succ n =>
      have : Epi (π.f 0) := ChainComplex.epi_augmentation_f_zero π
      let S : ShortComplex.ShortExactSequences C :=
        ⟨ShortComplex.kernelSequence (π.f 0),
          ShortComplex.kernelSequence_shortExact (π.f 0)⟩
      cases n with
      | zero =>
          let e₁ : (F.leftDerived 1).obj M ≅ Limits.kernel (F.map (kernel.ι (π.f 0))) :=
            F.leftDerivedOneIsoKernel S (by
              change IsZero ((F.leftDerived 1).obj (Q.X 0))
              exact hQ 0 0)
          exact e₁ ≪≫ (ChainComplex.homologyOneIsoOfPreservedKernelTail F π).symm
      | succ n =>
          let Q' : ChainComplex C ℕ := Q.restriction ChainComplex.kernelTailEmbedding
          let π' : Q' ⟶ (ChainComplex.single₀ C).obj (Limits.kernel (π.f 0)) :=
            ChainComplex.kernelTailAugmentation π
          have : QuasiIso π' := ChainComplex.quasiIso_kernelTailAugmentation π
          have hQ' : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (Q'.X q)) := by
            intro q i
            exact IsZero.of_iso (hQ (q + 1) i)
              ((F.leftDerived (i + 1)).mapIso
                (Q.restrictionXIso ChainComplex.kernelTailEmbedding
                  (ChainComplex.kernelTailEmbedding_f q)).symm)
          let eδ : (F.leftDerived (n + 2)).obj M ≅
              (F.leftDerived (n + 1)).obj (Limits.kernel (π.f 0)) :=
            F.leftDerivedDeltaFunctor.connectingIsoOfIsZeroMiddle (n + 1) S
              (by
                change IsZero ((F.leftDerived (n + 1)).obj (Q.X 0))
                exact hQ 0 n)
              (by
                change IsZero ((F.leftDerived (n + 2)).obj (Q.X 0))
                exact hQ 0 (n + 1))
          let eQ' := leftDerivedObjIsoHomologyOfAcyclicResolution F Q' π' hQ' (n + 1)
          let K : ChainComplex D ℕ :=
            (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
          let eH : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q').homology
                (n + 1) ≅ K.homology (n + 2) := by
            change (K.restriction ChainComplex.kernelTailEmbedding).homology (n + 1) ≅
              K.homology (n + 2)
            exact K.restrictionHomologyIso ChainComplex.kernelTailEmbedding
              (n + 2) (n + 1) n
              (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
              (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
              (i' := n + 3) (j' := n + 2) (k' := n + 1) rfl rfl rfl
              (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
              (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))
          exact eδ ≪≫ eQ' ≪≫ eH
termination_by n
decreasing_by omega

end CategoryTheory.Functor
