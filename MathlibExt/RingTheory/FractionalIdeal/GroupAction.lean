/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Group actions on fractional ideals

This module constructs the action of a group of ring automorphisms on fractional
ideals of a fraction ring.
-/

@[expose] public section

open scoped nonZeroDivisors
open scoped Pointwise

namespace FractionalIdeal

variable (R K : Type*) [CommRing R] [IsDomain R] [CommRing K]
  [Algebra R K] [IsFractionRing R K]

/-- **Ring automorphisms act on fractional ideals.** Let $R$ be a commutative domain
and $K$ a field of fractions of $R$. For a ring automorphism $\sigma$ of $R$, let $\tilde\sigma$
be the automorphism of $K$ extending $\sigma$. Sending $\sigma$ to the map
$I \mapsto \tilde\sigma(I)$ on fractional ideals of $R$ in $K$ defines a group homomorphism from
the group of ring automorphisms of $R$ to the group of ring automorphisms of the semiring of
fractional ideals of $R$ in $K$. -/
noncomputable def ringEquivOfRingEquivHom :
    RingAut R →* RingAut (FractionalIdeal R⁰ K) where
  toFun σ := FractionalIdeal.ringEquivOfRingEquiv K K σ
  map_one' := FractionalIdeal.ringEquivOfRingEquiv_refl K
  map_mul' σ τ := FractionalIdeal.ringEquivOfRingEquiv_trans K K K τ σ

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [MulSemiringAction G R]

/-- The `MulSemiringAction` on fractional ideals induced by that on the base ring. -/
noncomputable instance instMulSemiringAction :
    MulSemiringAction G (FractionalIdeal R⁰ K) :=
  MulSemiringAction.compHom _ ((ringEquivOfRingEquivHom R K).comp
    (MulSemiringAction.toRingAut G R))

/-- **Action on invertible fractional ideals.** Let a group $G$ act on a commutative domain $R$
by ring automorphisms, let $K$ be a field of fractions of $R$, and let $G$ act on fractional
ideals of $R$ in $K$ by $g \cdot I = \tilde\sigma_g(I)$, where $\tilde\sigma_g$ is the
automorphism of $K$ extending $r \mapsto g \cdot r$. This induces an action of $G$ on the group
of invertible fractional ideals: $g$ sends an invertible fractional ideal $I$ to $g \cdot I$,
whose inverse is $g \cdot I^{-1}$. This action respects products and fixes the unit fractional
ideal $R$. -/
noncomputable abbrev unitsMulDistribMulAction :
    MulDistribMulAction G (FractionalIdeal R⁰ K)ˣ :=
  Units.mulDistribMulActionRight

scoped[FractionalIdealUnits] attribute [instance]
  FractionalIdeal.unitsMulDistribMulAction

open scoped FractionalIdealUnits

/-- **Translating an invertible fractional ideal.** Let a group $G$ act on a commutative domain
$R$ by ring automorphisms, let $K$ be a field of fractions of $R$, and let $G$ act on fractional
ideals of $R$ in $K$ by $g \cdot I = \tilde\sigma_g(I)$, where $\tilde\sigma_g$ is the
automorphism of $K$ extending $r \mapsto g \cdot r$. For every $g \in G$ and every invertible
fractional ideal $I$, the translate of $I$ under the induced action on invertible fractional
ideals has underlying fractional ideal $g \cdot I$. -/
@[simp]
theorem units_smul_val (g : G) (I : (FractionalIdeal R⁰ K)ˣ) :
    ((g • I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      g • (I : FractionalIdeal R⁰ K) :=
  rfl

/-- **The action on fractional ideals is by images.** Let a group $G$ act on a commutative domain
$R$ by ring automorphisms and let $K$ be a field of fractions of $R$. For $g \in G$ let
$\tilde\sigma_g$ be the automorphism of $K$ extending the automorphism $r \mapsto g \cdot r$ of
$R$. Then for every $g \in G$ and every fractional ideal $I$ of $R$ in $K$, the induced action
satisfies $g \cdot I = \tilde\sigma_g(I)$, the image of $I$ under $\tilde\sigma_g$. -/
@[simp]
theorem smul_def (g : G) (I : FractionalIdeal R⁰ K) :
    g • I =
      FractionalIdeal.ringEquivOfRingEquiv K K
        (MulSemiringAction.toRingAut G R g) I :=
  rfl

/-- **Elements of a translated fractional ideal are images.** Let a group $G$ act on a
commutative domain $R$ by ring automorphisms, let $K$ be a field of fractions of $R$, and let $G$
act on fractional ideals of $R$ in $K$ by $g \cdot I = \tilde\sigma_g(I)$, where $\tilde\sigma_g$
is the automorphism of $K$ extending $r \mapsto g \cdot r$. For every $g \in G$, every fractional
ideal $I$ and every $x \in K$, we have $x \in g \cdot I$ if and only if $\tilde\sigma_g(y) = x$
for some $y \in I$. -/
theorem mem_smul_iff_exists (g : G) (I : FractionalIdeal R⁰ K) (x : K) :
    x ∈ g • I ↔ ∃ y ∈ I,
      IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g) y = x := by
  rw [smul_def]
  change x ∈ (ringEquivOfRingEquiv K K (MulSemiringAction.toRingAut G R g) I).val ↔ _
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply_val, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- **Membership in a translated fractional ideal.** Let a group $G$ act on a commutative domain
$R$ by ring automorphisms, let $K$ be a field of fractions of $R$, and let $G$ act on fractional
ideals of $R$ in $K$ by $g \cdot I = \tilde\sigma_g(I)$, where $\tilde\sigma_g$ is the
automorphism of $K$ extending $r \mapsto g \cdot r$. For every $g \in G$, every fractional ideal
$I$ and every $x \in K$, we have $x \in g \cdot I$ if and only if
$\tilde\sigma_g^{-1}(x) \in I$. -/
theorem mem_smul_iff (g : G) (I : FractionalIdeal R⁰ K) (x : K) :
    x ∈ g • I ↔
      (IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g)).symm x ∈ I := by
  let F := IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
    (MulSemiringAction.toRingAut G R g)
  rw [mem_smul_iff_exists (R := R) (K := K)]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← h, F.symm_apply_apply]
    exact hy
  · intro hx
    exact ⟨F.symm x, hx, F.apply_symm_apply x⟩

/-- **Translating an integral ideal.** Let a group $G$ act on a commutative domain $R$ by ring
automorphisms, let $K$ be a field of fractions of $R$, and let $G$ act on fractional ideals of
$R$ in $K$ by $g \cdot J = \tilde\sigma_g(J)$, where $\tilde\sigma_g$ is the automorphism of $K$
extending $r \mapsto g \cdot r$. For every $g \in G$ and every ideal $I$ of $R$, the translate
$g \cdot I$ of $I$ viewed as a fractional ideal is the ideal $\{g \cdot a : a \in I\}$ of $R$
viewed as a fractional ideal. -/
@[simp]
theorem smul_coeIdeal (g : G) (I : Ideal R) :
    g • (I : FractionalIdeal R⁰ K) =
      ((g • I : Ideal R) : FractionalIdeal R⁰ K) := by
  ext x
  simp only [mem_smul_iff_exists, mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hx⟩
    have h : IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g) (algebraMap R K a) =
        algebraMap R K (g • a) := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      rfl
    refine ⟨g • a, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mpr ?_, ?_⟩
    · simpa using ha
    · rw [← hx, h]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have h : IsFractionRing.ringEquivOfRingEquiv
        (MulSemiringAction.toRingAut G R g) (algebraMap R K (g⁻¹ • b)) =
        algebraMap R K b := by
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      congr 1
      exact smul_inv_smul g b
    exact ⟨_, ⟨_, hb, rfl⟩, h⟩

end FractionalIdeal
