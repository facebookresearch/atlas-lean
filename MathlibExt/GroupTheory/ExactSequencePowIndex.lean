/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact.lean`
and
`P2M/Sol/S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MonoidHom

/-- For a short exact sequence of commutative groups `U → G → F` in which
the quotient `F` has no nontrivial element killed by the `n`-th power map,
the index of the `n`-th powers in `G` is the product of the corresponding
indices in `F` and in `U`. The torsion hypothesis on `F` is what lets an
element of `G` whose `n`-th power lies in the kernel be adjusted back into
the image of `U`. -/
public theorem index_range_powMonoidHom_eq_mul_of_exact
    {G U F : Type*} [CommGroup G] [CommGroup U] [CommGroup F]
    (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι)
    (hφ : Function.Surjective φ) (hexact : ι.range = φ.ker) {n : ℕ}
    (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index
        * (powMonoidHom n : U →* U).range.index := by
  classical
  have h1 : φ.ker ⊔ (powMonoidHom n : G →* G).range
      = ((powMonoidHom n : F →* F).range).comap φ := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro g hg
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]; exact one_mem _
      · rintro _ ⟨g, rfl⟩
        rw [Subgroup.mem_comap, powMonoidHom_apply, map_pow]
        exact ⟨φ g, rfl⟩
    · intro g hg
      rw [Subgroup.mem_comap] at hg
      obtain ⟨z, hz⟩ := hg
      obtain ⟨g', rfl⟩ := hφ z
      rw [powMonoidHom_apply, ← map_pow] at hz
      refine Subgroup.mem_sup.2
        ⟨g * (g' ^ n)⁻¹, ?_, g' ^ n, ⟨g', rfl⟩, inv_mul_cancel_right g (g' ^ n)⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hz, mul_inv_cancel]
  have h3 : ((powMonoidHom n : G →* G).range).relIndex
        (φ.ker ⊔ (powMonoidHom n : G →* G).range)
      = ((powMonoidHom n : G →* G).range ⊓ φ.ker).relIndex φ.ker := by
    rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_right]
  have h4 : (powMonoidHom n : G →* G).range ⊓ φ.ker
      = ((powMonoidHom n : U →* U).range).map ι := by
    apply le_antisymm
    · intro x hx'
      obtain ⟨⟨g, rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx'
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow] at hx
      have hg' : g ∈ ι.range := by rw [hexact]; exact hF _ hx
      obtain ⟨u, rfl⟩ := hg'
      exact ⟨u ^ n, ⟨u, rfl⟩, by rw [map_pow, powMonoidHom_apply]⟩
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨⟨ι u, by
        rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]⟩, ?_⟩
      rw [← hexact]; exact ⟨u ^ n, by rw [powMonoidHom_apply, map_pow]⟩
  have h5 : (((powMonoidHom n : U →* U).range).map ι).relIndex φ.ker
      = ((powMonoidHom n : U →* U).range).index := by
    rw [← hexact, MonoidHom.range_eq_map ι,
      MonoidHom.range_eq_map (powMonoidHom n : U →* U),
      ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective hι, Subgroup.relIndex_top_right]
  calc ((powMonoidHom n : G →* G).range).index
      = ((powMonoidHom n : G →* G).range).relIndex
            (φ.ker ⊔ (powMonoidHom n : G →* G).range)
          * (φ.ker ⊔ (powMonoidHom n : G →* G).range).index :=
        (Subgroup.relIndex_mul_index le_sup_right).symm
    _ = ((powMonoidHom n : G →* G).range ⊓ φ.ker).relIndex φ.ker
          * ((powMonoidHom n : F →* F).range).index := by
          rw [h3, h1, Subgroup.index_comap_of_surjective _ hφ]
    _ = _ := by rw [h4, h5, mul_comm]

end MonoidHom
