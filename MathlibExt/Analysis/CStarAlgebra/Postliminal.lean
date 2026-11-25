/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# The shared nonunital postliminal/Type-I representation criterion

A nonzero irreducible representation contains every actual compact operator
in the original complete complex Hilbert-space norm. The operator-set
irreducibility clause is the literal closed-invariant-submodule criterion.
No representation, compact ideal or source-theorem output is selected.
The representation universe remains an independent explicit parameter;
source callers choose their original adequate Hilbert test universe.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace CStarAlgebra
universe uA uH

/-- **Postliminal nonunital C*-algebra.** A nonunital complex C*-algebra `A` is postliminal when every
nonzero irreducible nonunital star representation `π : A → B(H)` on a complete complex Hilbert space
has range containing all compact operators on `H`. Irreducibility means that the only closed
complex-linear subspaces invariant under all `π(a)` are zero and the whole space. -/
def IsPostliminal (A : Type uA) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
    pi ≠ 0 →
      (∀ K : Submodule ℂ H, IsClosed (K : Set H) →
        (∀ T ∈ Set.range pi, ∀ x ∈ K, T x ∈ K) → K = ⊥ ∨ K = ⊤) →
      ({T : H →L[ℂ] H | IsCompactOperator T} : Set (H →L[ℂ] H)) ⊆ Set.range pi

/-- **Nonzero representations have nonzero Hilbert space.** For a nonunital complex C*-algebra `A`, a
complete complex Hilbert space `H`, and a nonzero nonunital complex star representation `π : A →
B(H)`, the space `H` is nontrivial. -/
theorem nontrivial_of_nonzero_representation
    {A : Type uA} [NonUnitalCStarAlgebra A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hpi : pi ≠ 0) : Nontrivial H := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · haveI : Subsingleton H := hH
    apply False.elim
    apply hpi
    apply NonUnitalStarAlgHom.ext
    intro a
    apply ContinuousLinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  · exact hH

/-- **Irreducible-representation characterization of postliminality.** A nonunital complex C*-algebra
`A` is postliminal exactly when every nonzero nonunital star representation `π : A → B(H)` on a
nontrivial complete complex Hilbert space, whose only closed invariant complex-linear subspaces are
zero and `H`, has every compact operator in its range. -/
theorem isPostliminal_iff_nonzero_irreducible_criterion
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    IsPostliminal.{uA, uH} A ↔
      ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        pi ≠ 0 →
          (Nontrivial H ∧ ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
            (∀ (a : A) ⦃x : H⦄, x ∈ K → pi a x ∈ K) → K = ⊥ ∨ K = ⊤) →
          ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, pi a = T := by
  constructor
  · intro h H _ _ _ pi hpi hirr T hT
    apply h pi hpi ?_ hT
    intro K hK hInv
    apply hirr.2 K hK
    intro a x hx
    exact hInv (pi a) ⟨a, rfl⟩ x hx
  · intro h H _ _ _ pi hpi hirr T hT
    refine h H pi hpi ⟨nontrivial_of_nonzero_representation pi hpi, ?_⟩ T hT
    intro K hK hInv
    apply hirr K hK
    rintro U ⟨a, rfl⟩ x hx
    exact hInv a hx

/-- **Irreducible nonzero representations preserve the unit.** Let `A` be a unital complex C*-algebra
and `H` a complete complex Hilbert space. If a nonzero nonunital complex star homomorphism `π : A →
B(H)` has no proper nonzero closed invariant complex-linear subspace, then `π(1)` is the identity
operator on `H`. -/
theorem map_one_eq_one_of_nonzero_irreducible_representation
    {A : Type uA} [CStarAlgebra A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hpi : pi ≠ 0)
    (hirr : ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
      (∀ (a : A) ⦃x : H⦄, x ∈ K → pi a x ∈ K) → K = ⊥ ∨ K = ⊤) :
    pi 1 = 1 := by
  let p : H →L[ℂ] H := pi 1
  have hp : IsIdempotentElem p := by
    change pi 1 * pi 1 = pi 1
    rw [← map_mul, one_mul]
  have hleft (a : A) : p * pi a = pi a := by
    change pi 1 * pi a = pi a
    rw [← map_mul, one_mul]
  have hmem (a : A) (x : H) : pi a x ∈ p.range := by
    refine ⟨pi a x, ?_⟩
    exact congrArg (fun T : H →L[ℂ] H => T x) (hleft a)
  have hclosed : IsClosed (p.range : Set H) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hp
  rcases hirr p.range hclosed (fun a x _ => hmem a x) with hzero | hfull
  · exact False.elim (hpi (by
      apply NonUnitalStarAlgHom.ext
      intro a
      apply ContinuousLinearMap.ext
      intro x
      have hx := hmem a x
      rw [hzero] at hx
      exact (Submodule.mem_bot ℂ).mp hx))
  · apply ContinuousLinearMap.ext
    intro x
    change p x = x
    have hx : x ∈ p.range := by rw [hfull]; trivial
    rcases hx with ⟨y, hy⟩
    change p y = x at hy
    have hfix : p (p y) = p y :=
      congrArg (fun T : H →L[ℂ] H => T y) (show p * p = p from hp)
    simpa only [hy] using hfix

/-- **Unital representations on a nonzero space are nonzero.** For a unital complex C*-algebra `A` and a
nontrivial complete complex Hilbert space `H`, a unital complex star representation `π : A → B(H)`
is nonzero when regarded as a nonunital star homomorphism. -/
theorem nonzero_toNonUnitalStarAlgHom
    {A : Type uA} [CStarAlgebra A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : pi.toNonUnitalStarAlgHom ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have h := congrArg (fun rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) => rho 1 x) hzero
  change pi 1 x = 0 at h
  rw [map_one, one_apply_eq_self] at h
  exact hx h

/-- **Unital representation criterion for postliminality.** A unital complex C*-algebra `A` is
postliminal exactly when every irreducible unital star representation on a nontrivial complete
complex Hilbert space has all compact operators in its range. Irreducibility here is stated for
closed invariant complex-linear subspaces. -/
theorem isPostliminal_iff_unital_irreducible_criterion
    (A : Type uA) [CStarAlgebra A] :
    IsPostliminal.{uA, uH} A ↔
      ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
        (Nontrivial H ∧ ∀ K : Submodule ℂ H, IsClosed (K : Set H) →
          (∀ (a : A) ⦃x : H⦄, x ∈ K → pi a x ∈ K) → K = ⊥ ∨ K = ⊤) →
        ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, pi a = T := by
  constructor
  · intro h H _ _ _ pi hirr
    haveI : Nontrivial H := hirr.1
    exact (isPostliminal_iff_nonzero_irreducible_criterion.{uA, uH} A).mp h H
      pi.toNonUnitalStarAlgHom (nonzero_toNonUnitalStarAlgHom pi) hirr
  · intro h
    apply (isPostliminal_iff_nonzero_irreducible_criterion.{uA, uH} A).mpr
    intro H _ _ _ pi hpi hirr T hT
    have hunit := map_one_eq_one_of_nonzero_irreducible_representation pi hpi hirr.2
    let rho : A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
      { toFun := pi
        map_zero' := map_zero pi
        map_one' := hunit
        map_add' := map_add pi
        map_mul' := map_mul pi
        commutes' := by
          intro c
          rw [Algebra.algebraMap_eq_smul_one, map_smul, hunit,
            Algebra.algebraMap_eq_smul_one]
        map_star' := map_star pi }
    exact h H rho hirr T hT

end CStarAlgebra
