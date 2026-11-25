/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Torsion in finitely generated abelian groups

Code-derived port of `AbelianGroups.torsion_subgroup_structure` from
`v1/Atlas/AlgebraNotes/code/AbelianGroups.lean` at commit
`8de8f74fa5760eb8b768a9804494ca2ab631cf87`, lines 44–72.
The archived formalization and its original license/provenance remain in `v1/`
(the original license text is `v1/LICENSE`). This records equivalence to the
archived Lean statement, not verification against the printed textbook.
-/

set_option autoImplicit false

open scoped DirectSum

namespace AddCommGroup

/-- **Torsion subgroup of a finitely generated abelian group is finitely generated.** If $A$ is a
finitely generated abelian group, then its torsion subgroup is finitely generated. -/
public theorem fg_torsion (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    AddGroup.FG (torsion A) := by
  let : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let : IsNoetherian ℤ A := isNoetherian_of_isNoetherianRing_of_finite ℤ A
  have hfg : (Submodule.torsion ℤ A).FG := IsNoetherian.noetherian _
  rw [AddGroup.fg_iff_addSubgroup_fg, ← Submodule.torsion_int]
  exact (Submodule.fg_iff_addSubgroup_fg _).mp hfg

/-- **Torsion subgroup of a finitely generated abelian group is finite.** If $A$ is a finitely
generated abelian group, then its torsion subgroup is finite. -/
public theorem finite_torsion_of_fg (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Finite (torsion A) := by
  let : AddGroup.FG (torsion A) := fg_torsion A
  apply finite_of_fg_isAddTorsion
  intro x
  have hx : IsOfFinAddOrder (x : A) := (mem_torsion (x : A)).mp x.property
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨n, hn, Subtype.ext (by simpa using hnx)⟩

/-- **Torsion subgroup of a finitely generated abelian group as a sum of cyclic groups.** If $A$
is a finitely generated abelian group, then there exist a natural number $n$ and positive
integers $d_1, \dots, d_n$ such that the torsion subgroup of $A$ is isomorphic to the direct sum
$\mathbb{Z}/d_1\mathbb{Z} \oplus \cdots \oplus \mathbb{Z}/d_n\mathbb{Z}$ of finite cyclic groups. -/
public theorem torsion_equiv_directSum_zmod_of_fg (A : Type*) [AddCommGroup A]
    [AddGroup.FG A] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, 0 < d i),
      Nonempty (torsion A ≃+ (⨁ i : Fin n, ZMod (d i))) := by
  classical
  let : Finite (torsion A) := finite_torsion_of_fg A
  obtain ⟨ι, fι, d, hd, ⟨e⟩⟩ := equiv_directSum_zmod_of_finite' (torsion A)
  let g : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  exact ⟨Fintype.card ι, fun i ↦ d (g.symm i), fun i ↦ (hd (g.symm i)).pos,
    ⟨e.trans (DirectSum.equivCongrLeft g)⟩⟩

end AddCommGroup
