/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteTorusBoundaryWord

/-! # Finite-torus kernel landing

For an arbitrary field `F` and arbitrary rank `n : ℕ` with no rank bound,
`ker toStableE ⊓ finiteTorusSubgroup n ≤ torusCocycleSubgroup`.

The proof splits the infimum, factors the finite-torus element by the accepted
`finiteTorus_eq_cocycle_mul_boundaryTorusWord`, pushes the head-left cocycle
defect into the kernel by `torusCocycleSubgroup_le_ker_toStableE`, collects the
boundary word by the accepted `boundaryTorusWord_eq_cocycle_mul_boundaryTorusProd`,
transports the resulting `boundaryTorusProd n u` through
`toStableE_boundaryTorusProd`, recovers `u = 1` from the accepted injectivity
`toStableE_torus_fin_last_piHom_injective n`, and closes by the locally reproved
all-one product fact below. Uniform for `n = 0`, `n = 1`, and larger ranks.

Nonclaims: no finite-stage generation, no full kernel equality, no Matsumoto
inverse, and no naturality are proved here.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

/-- Local all-one evaluation of `boundaryTorusProd`.

The accepted all-one fact is intentionally private, so it is reproved here from
public `boundaryTorusProd_eq_finRange` and `torus_one`. -/
private theorem boundaryTorusProd_allOne_vec {F : Type u} [Field F] (n : ℕ) :
    boundaryTorusProd (F := F) n (1 : Fin n → Fˣ) = 1 := by
  have hfun : (1 : Fin n → Fˣ) = fun _ : Fin n => (1 : Fˣ) := rfl
  rw [hfun, boundaryTorusProd_eq_finRange]
  simp [torus_one]

/-- Finite-torus kernel elements land in the torus-cocycle subgroup.

For `[Field F]` and arbitrary `n : ℕ` with no rank bound, every
`g ∈ ker toStableE ⊓ finiteTorusSubgroup n` lies in `torusCocycleSubgroup`.

Nonclaims: only this landing inclusion; no finite-stage induction, full kernel
equality, inverse, or naturality claim. -/
public theorem ker_toStableE_inf_finiteTorus_le_torusCocycleSubgroup
    {F : Type u} [Field F] {n : ℕ} :
    MonoidHom.ker (toStableE (R := F)) ⊓ finiteTorusSubgroup (R := F) n ≤
      torusCocycleSubgroup (F := F) := by
  intro g hg
  obtain ⟨hgker, hgtor⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨c₁, hc₁, L, hg_eq⟩ := finiteTorus_eq_cocycle_mul_boundaryTorusWord hgtor
  have hg_one : toStableE (R := F) g = 1 := MonoidHom.mem_ker.mp hgker
  have hc₁_one : toStableE (R := F) c₁ = 1 :=
    MonoidHom.mem_ker.mp (torusCocycleSubgroup_le_ker_toStableE (F := F) hc₁)
  have hword_one : toStableE (R := F) (boundaryTorusWord (F := F) L) = 1 := by
    have hmap : toStableE (R := F) c₁ *
        toStableE (R := F) (boundaryTorusWord (F := F) L) = 1 := by
      rw [← map_mul, ← hg_eq]
      exact hg_one
    rw [hc₁_one, one_mul] at hmap
    exact hmap
  obtain ⟨c₂, hc₂, hword_eq⟩ :=
    boundaryTorusWord_eq_cocycle_mul_boundaryTorusProd (F := F) L
  have hc₂_one : toStableE (R := F) c₂ = 1 :=
    MonoidHom.mem_ker.mp (torusCocycleSubgroup_le_ker_toStableE (F := F) hc₂)
  have hprod_one : toStableE (R := F)
      (boundaryTorusProd (F := F) n
        (fun i => boundaryTorusCoord (F := F) i L)) = 1 := by
    have hmap : toStableE (R := F) c₂ *
        toStableE (R := F) (boundaryTorusProd (F := F) n
          (fun i => boundaryTorusCoord (F := F) i L)) = 1 := by
      rw [← map_mul, ← hword_eq]
      exact hword_one
    rw [hc₂_one, one_mul] at hmap
    exact hmap
  have hpi_one : toStableE_torus_fin_last_piHom (F := F) n
      (fun i => boundaryTorusCoord (F := F) i L) = 1 := by
    rw [← toStableE_boundaryTorusProd (F := F) n _, hprod_one]
  have hu_one : (fun i => boundaryTorusCoord (F := F) i L) = 1 := by
    have h_eq : toStableE_torus_fin_last_piHom (F := F) n
          (fun i => boundaryTorusCoord (F := F) i L) =
        toStableE_torus_fin_last_piHom (F := F) n 1 := by
      rw [hpi_one, map_one]
    exact toStableE_torus_fin_last_piHom_injective (F := F) n h_eq
  have hprod_eq_one : boundaryTorusProd (F := F) n
      (fun i => boundaryTorusCoord (F := F) i L) = 1 := by
    rw [hu_one]
    exact boundaryTorusProd_allOne_vec (F := F) n
  rw [hg_eq, hword_eq, hprod_eq_one, mul_one]
  exact (torusCocycleSubgroup (F := F)).mul_mem hc₁ hc₂

end StableSteinberg

end AlgebraicKTheory

end
