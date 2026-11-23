/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.RelativeCupCover

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

noncomputable section

universe u

namespace MathlibExtTest.Topology.Category.TopCat.RelativeCupCoverTests

open AlgebraicTopology

variable {X : TopCat.{u}} (A B : Set X)

/-- The forward left-subspace isomorphism forgets the intermediate union
subtype without changing the ambient point. -/
theorem relativeCupLeftIso_hom_apply_client
    (x : TopCat.of (relativeCupLeft A B)) :
    (relativeCupLeftIso A B).hom x = ⟨x.1.1, x.2⟩ := by
  exact relativeCupLeftIso_hom_apply A B x

/-- The inverse left-subspace isomorphism restores the canonical union
membership proof. -/
theorem relativeCupLeftIso_inv_apply_client (x : TopCat.of A) :
    (relativeCupLeftIso A B).inv x =
      ⟨⟨x.1, Set.mem_union_left B x.2⟩, x.2⟩ := by
  exact relativeCupLeftIso_inv_apply A B x

/-- The forward right-subspace isomorphism forgets the intermediate union
subtype without changing the ambient point. -/
theorem relativeCupRightIso_hom_apply_client
    (x : TopCat.of (relativeCupRight A B)) :
    (relativeCupRightIso A B).hom x = ⟨x.1.1, x.2⟩ := by
  exact relativeCupRightIso_hom_apply A B x

/-- The inverse right-subspace isomorphism restores the canonical union
membership proof. -/
theorem relativeCupRightIso_inv_apply_client (x : TopCat.of B) :
    (relativeCupRightIso A B).inv x =
      ⟨⟨x.1, Set.mem_union_right A x.2⟩, x.2⟩ := by
  exact relativeCupRightIso_inv_apply A B x

/-- The reassociated left triangle reaches the same ambient point through the
flat and nested subtype presentations. -/
theorem relativeCupLeftIso_hom_incl_assoc_client :
    (relativeCupLeftIso A B).hom ≫
          subspaceInclOfSubset (fun _ hx => Set.mem_union_left B hx) ≫
          subspaceIncl (A ∪ B : Set X) =
      subspaceIncl (relativeCupLeft A B) ≫
        subspaceIncl (A ∪ B : Set X) := by
  apply TopCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom
    (relativeCupLeftIso_hom_incl_assoc A B
      (subspaceIncl (A ∪ B : Set X))) x

/-- The reassociated right triangle reaches the same ambient point through the
flat and nested subtype presentations. -/
theorem relativeCupRightIso_hom_incl_assoc_client :
    (relativeCupRightIso A B).hom ≫
          subspaceInclOfSubset (fun _ hx => Set.mem_union_right A hx) ≫
          subspaceIncl (A ∪ B : Set X) =
      subspaceIncl (relativeCupRight A B) ≫
        subspaceIncl (A ∪ B : Set X) := by
  apply TopCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom
    (relativeCupRightIso_hom_incl_assoc A B
      (subspaceIncl (A ∪ B : Set X))) x

end MathlibExtTest.Topology.Category.TopCat.RelativeCupCoverTests
