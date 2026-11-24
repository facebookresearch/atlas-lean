/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.Prod

/-!
# Linear maps preserving the first summand

A linear map between products and a compatible map on the first summand
determine the relative map and off-diagonal part. The compatibility is the
first-inclusion square. These coordinates apply over an arbitrary
commutative ring with independent module universes.
-/

@[expose] public section

noncomputable section

universe u v w v' w' v'' w''

namespace exteriorPower.ProductFiltration

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {M' : Type v'} [AddCommGroup M'] [Module R M']
  {N' : Type w'} [AddCommGroup N'] [Module R N']

/-- The actual first-inclusion square; filtered preservation is a later conclusion. -/
structure FirstSummandMap where
  map : M × N →ₗ[R] M' × N'
  first : M →ₗ[R] M'
  first_commutes :
    map.comp (LinearMap.inl R M N) = (LinearMap.inl R M' N').comp first

namespace FirstSummandMap

variable (f : FirstSummandMap (R := R) (M := M) (N := N) (M' := M') (N' := N'))

/-- The actual relative map on the original second summand. -/
def relative : N →ₗ[R] N' :=
  (LinearMap.snd R M' N').comp (f.map.comp (LinearMap.inr R M N))

/-- The actual off-diagonal component, which is allowed to be nonzero. -/
def offDiagonal : N →ₗ[R] M' :=
  (LinearMap.fst R M' N').comp (f.map.comp (LinearMap.inr R M N))

theorem map_inl (x : M) : f.map (x, 0) = (f.first x, 0) :=
  LinearMap.congr_fun f.first_commutes x

theorem map_inr (y : N) : f.map (0, y) = (f.offDiagonal y, f.relative y) := rfl

/-- The original map is genuinely block triangular, not assumed block diagonal. -/
theorem map_pair (x : M) (y : N) :
    f.map (x, y) = (f.first x + f.offDiagonal y, f.relative y) := by
  have hpair : (x, y) = (x, 0) + (0, y) := by ext <;> simp
  rw [hpair, map_add, f.map_inl, f.map_inr]
  simp only [Prod.mk_add_mk, zero_add]

theorem relative_square :
    (LinearMap.snd R M' N').comp f.map = f.relative.comp (LinearMap.snd R M N) := by
  apply LinearMap.ext
  intro x
  have h := f.map_pair x.1 x.2
  have hs := congrArg (fun z : M' × N' => z.2) h
  exact hs

def id : FirstSummandMap (R := R) (M := M) (N := N) (M' := M) (N' := N) where
  map := LinearMap.id
  first := LinearMap.id
  first_commutes := by ext x <;> rfl

variable {M'' : Type v''} [AddCommGroup M''] [Module R M'']
  {N'' : Type w''} [AddCommGroup N''] [Module R N'']

/-- Compose the original square data; no new preservation certificate is chosen. -/
def comp (g : FirstSummandMap (R := R) (M := M') (N := N') (M' := M'') (N' := N'')) :
    FirstSummandMap (R := R) (M := M) (N := N) (M' := M'') (N' := N'') where
  map := g.map.comp f.map
  first := g.first.comp f.first
  first_commutes := by
    rw [LinearMap.comp_assoc, f.first_commutes, ← LinearMap.comp_assoc,
      g.first_commutes, LinearMap.comp_assoc]

/-- The relative maps compose as the actual induced maps modulo the first summands. -/
theorem relative_comp
    (g : FirstSummandMap (R := R) (M := M') (N := N') (M' := M'') (N' := N'')) :
    (f.comp g).relative = g.relative.comp f.relative := by
  ext y
  change (g.map (f.map (0, y))).2 = g.relative (f.relative y)
  rw [f.map_inr, g.map_pair]

end FirstSummandMap

end exteriorPower.ProductFiltration

end
