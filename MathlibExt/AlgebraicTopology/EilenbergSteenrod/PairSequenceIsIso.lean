/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact

/-!
# Isomorphisms forced by vanishing in the exact pair sequence

Adjacent zero objects in the long exact sequence of a pair force the
subspace or relative map between them to be an isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inclusion-induced absolute map is an isomorphism when relative
homology vanishes in its degree and the following degree. -/
theorem isIso_subspaceMap_of_isZero_relative
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSucc : IsZero ((E.Hₚ (k + 1)).obj P))
    (hSelf : IsZero ((E.Hₚ k).obj P)) :
    IsIso (E.subspaceMap k P) := by
  have hdeg : k + 1 - 1 = k := by omega
  have hExactMono := exact_boundary_subspaceMap E (k + 1) P
  let hMonoPrev : Mono (E.subspaceMap (k + 1 - 1) P) :=
    hExactMono.mono_g (hSucc.eq_of_src _ _)
  let _ : Mono (E.subspaceMap k P) := hdeg ▸ hMonoPrev
  have hExactEpi := exact_subspaceMap_toRelative E k P
  let _ : Epi (E.subspaceMap k P) :=
    hExactEpi.epi_f (hSelf.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (E.subspaceMap k P)

/-- The map from absolute to relative homology is an isomorphism when the
subspace homology vanishes in its degree and the preceding degree. -/
theorem isIso_toRelative_of_isZero_subspace
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSelf : IsZero ((E.H k).obj P.snd))
    (hPrev : IsZero ((E.H (k - 1)).obj P.snd)) :
    IsIso (E.toRelative k P) := by
  have hExactMono := exact_subspaceMap_toRelative E k P
  let _ : Mono (E.toRelative k P) :=
    hExactMono.mono_g (hSelf.eq_of_src _ _)
  have hExactEpi := exact_toRelative_boundary E k P
  let _ : Epi (E.toRelative k P) :=
    hExactEpi.epi_f (hPrev.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (E.toRelative k P)

/-- The map from absolute to relative homology is an isomorphism when the
subspace homology vanishes in its degree and the preceding-degree subspace
map is an isomorphism. -/
theorem isIso_toRelative_of_isZero_subspace_of_isIso_prev_subspaceMap
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSelf : IsZero ((E.H k).obj P.snd))
    (hPrev : IsIso (E.subspaceMap (k - 1) P)) :
    IsIso (E.toRelative k P) := by
  have hExactMono := exact_subspaceMap_toRelative E k P
  let _ : Mono (E.toRelative k P) :=
    hExactMono.mono_g (hSelf.eq_of_src _ _)
  have hBoundary : E.boundary k P = 0 := by
    rcases hPrev.out with ⟨g, hfg, -⟩
    calc
      E.boundary k P = E.boundary k P ≫ 𝟙 _ := by rw [Category.comp_id]
      _ = E.boundary k P ≫ (E.subspaceMap (k - 1) P ≫ g) := by rw [hfg]
      _ = (E.boundary k P ≫ E.subspaceMap (k - 1) P) ≫ g := by
        rw [Category.assoc]
      _ = 0 := by rw [boundary_comp_subspaceMap, Limits.zero_comp]
  have hExactEpi := exact_toRelative_boundary E k P
  let _ : Epi (E.toRelative k P) := hExactEpi.epi_f hBoundary
  exact isIso_of_mono_of_epi (E.toRelative k P)

/-- The inclusion-induced absolute isomorphism supplied by adjacent relative
vanishing. -/
noncomputable def subspaceMapIsoOfIsZeroRelative
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSucc : IsZero ((E.Hₚ (k + 1)).obj P))
    (hSelf : IsZero ((E.Hₚ k).obj P)) :
    (E.H k).obj P.snd ≅ (E.H k).obj P.fst := by
  let _ : IsIso (E.subspaceMap k P) :=
    isIso_subspaceMap_of_isZero_relative E k P hSucc hSelf
  exact asIso (E.subspaceMap k P)

@[simp]
theorem subspaceMapIsoOfIsZeroRelative_hom
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSucc : IsZero ((E.Hₚ (k + 1)).obj P))
    (hSelf : IsZero ((E.Hₚ k).obj P)) :
    (subspaceMapIsoOfIsZeroRelative E k P hSucc hSelf).hom =
      E.subspaceMap k P :=
  rfl

/-- The absolute-to-relative isomorphism supplied by adjacent subspace
vanishing. -/
noncomputable def toRelativeIsoOfIsZeroSubspace
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSelf : IsZero ((E.H k).obj P.snd))
    (hPrev : IsZero ((E.H (k - 1)).obj P.snd)) :
    (E.H k).obj P.fst ≅ (E.Hₚ k).obj P := by
  let _ : IsIso (E.toRelative k P) :=
    isIso_toRelative_of_isZero_subspace E k P hSelf hPrev
  exact asIso (E.toRelative k P)

@[simp]
theorem toRelativeIsoOfIsZeroSubspace_hom
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (k : ℤ) (P : TopPair.{w})
    (hSelf : IsZero ((E.H k).obj P.snd))
    (hPrev : IsZero ((E.H (k - 1)).obj P.snd)) :
    (toRelativeIsoOfIsZeroSubspace E k P hSelf hPrev).hom =
      E.toRelative k P :=
  rfl

end TopPair.HomologyTheoryData.IsExact
