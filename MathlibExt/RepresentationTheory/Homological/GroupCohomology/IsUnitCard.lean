/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Invariants

/-!
# Cohomology of a finite group whose order is a unit

Let `k` be a commutative ring and `G` a finite group such that `#G` (`Nat.card G`) is a unit
in `k`. Then the trivial representation `k` is projective in `Rep k G`, and consequently
`Hⁿ(G, A) = 0` for every `A : Rep k G` and every `n ≥ 1`.

The projectivity is proved by averaging: given an epimorphism `e : X ⟶ E` and a map
`f : k ⟶ E`, choose `x` with `e x = f 1` and replace it by its average
`(#G)⁻¹ • ∑ g, ρ(g) x`, which is `G`-invariant and still maps to the invariant vector `f 1`.
The vanishing then follows from `Hⁿ(G, A) ≅ Extⁿ(k, A)`, exactly as in Mathlib's
`isZero_groupCohomology_succ_of_subsingleton`.

For `k = ZMod p` the hypothesis holds whenever `p` is coprime to `#G`; `p` need not be prime.
This is the form used in B. H. Gross, *Kolyvagin's work on modular elliptic curves*,
in *L-functions and arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153,
Cambridge Univ. Press, 1991, 235–256, §9, p. 249, for a group of order prime to `p` acting
on an `𝔽_p`-module.

The Lean statements are for representations over a commutative ring `k` in which `#G` is a
unit. They do not cover the more general statement for an arbitrary `ℤ[G]`-module on which
multiplication by `#G` is bijective.

## Main results

* `Rep.trivial_projective_of_isUnit_natCard`: `k` is projective in `Rep k G` when `#G` is a
  unit in `k`.
* `groupCohomology.isZero_succ_of_isUnit_natCard`: `Hⁿ⁺¹(G, A) = 0` when `#G` is a unit in `k`.
* `groupCohomology.isZero_succ_zmod_of_coprime_natCard`: `Hⁿ⁺¹(G, A) = 0` for
  `A : Rep (ZMod p) G` when `p` is coprime to `#G`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Rep

/-- Let `k` be a commutative ring and `G` a finite group such that `#G` (`Nat.card G`) is a
unit in `k`. Then the trivial representation `Rep.trivial k G k` is a projective object of
`Rep k G`. -/
theorem trivial_projective_of_isUnit_natCard {k G : Type u} [CommRing k] [Group G] [Finite G]
    (h : IsUnit (Nat.card G : k)) : Projective (Rep.trivial k G k) where
  factors {X E} f e he := by
    have := Fintype.ofFinite G
    let : Invertible (Fintype.card G : k) := (Nat.card_eq_fintype_card (α := G) ▸ h).invertible
    obtain ⟨x, hx⟩ := (Rep.epi_iff_surjective e).1 he (f.hom (1 : k))
    have hy : X.ρ.averageMap x ∈ X.ρ.invariants := X.ρ.averageMap_invariant x
    refine ⟨Rep.ofHom (ρ := Representation.trivial k G k) (σ := X.ρ)
      ⟨LinearMap.toSpanSingleton k X (X.ρ.averageMap x), fun g => ?_⟩, ?_⟩
    · ext
      simpa [-Representation.averageMap] using (hy g).symm
    · have hf : f.hom (1 : k) ∈ E.ρ.invariants := fun g => by
        simpa using (Rep.hom_comm_apply f g (1 : k)).symm
      have he' : e.hom (X.ρ.averageMap x) = E.ρ.averageMap (e.hom x) := by
        simp [GroupAlgebra.average, map_sum, Rep.hom_comm_apply]
      refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext_ring ?_
      simp [-Representation.averageMap, he', hx, E.ρ.averageMap_id _ hf]

end Rep

namespace groupCohomology

/-- Let `k` be a commutative ring and `G` a finite group such that `#G` (`Nat.card G`) is a
unit in `k`. Then for every `A : Rep k G` and every `n : ℕ`, the group cohomology
`Hⁿ⁺¹(G, A)` is zero.

This is the vanishing `Hⁿ(Z, M) = 0` for `n ≥ 1` used in B. H. Gross, *Kolyvagin's work on
modular elliptic curves*, §9, p. 249, stated for representations over a commutative ring in
which the group order is a unit. -/
theorem isZero_succ_of_isUnit_natCard {k G : Type u} [CommRing k] [Group G] [Finite G]
    (h : IsUnit (Nat.card G : k)) (A : Rep.{u} k G) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  have := Rep.trivial_projective_of_isUnit_natCard h
  (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso <| groupCohomologyIsoExt _ _

/-- Let `p` be a natural number and `G` a finite group with `p` coprime to `#G`
(`Nat.card G`); `p` need not be prime. Then for every `A : Rep (ZMod p) G` and every
`n : ℕ`, the group cohomology `Hⁿ⁺¹(G, A)` is zero. -/
theorem isZero_succ_zmod_of_coprime_natCard {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Coprime (Nat.card G)) (A : Rep (ZMod p) G) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  isZero_succ_of_isUnit_natCard ((ZMod.isUnit_iff_coprime _ _).2 hp.symm) A n

end groupCohomology

end
