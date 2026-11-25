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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# AF algebras by countable finite-dimensional exhaustions

An AF algebra has a countable increasing sequence of actual closed,
finite-dimensional star subalgebras with dense union. Their operations,
norms and topologies are inherited from the given coefficient algebra.
This is the countable exhaustion formulation of Murphy, Section 6.2.

Finite-set approximation without separability is a broader condition; it
is not substituted for the countable exhaustion predicate here. Images of
finite-dimensional stages give an exhaustion even when the connecting
maps are not injective.
-/

@[expose] public section

open Set

namespace CStarAlgebra

universe u v

/-- **Closed finite-dimensional C*-subalgebra.** For a nonunital complex C*-algebra `A` and a nonunital
star subalgebra `B ⊆ A`, this means that `B` is closed in the norm topology of `A` and
finite-dimensional as a complex vector space, with its inherited norm. -/
def IsFiniteDimensionalSubalgebra
    {A : Type u} [NonUnitalCStarAlgebra A]
    (B : NonUnitalStarSubalgebra ℂ A) : Prop :=
  IsClosed (B : Set A) ∧ FiniteDimensional ℂ B

/-- **Approximately finite-dimensional C*-algebras.** A nonunital complex
C*-algebra `A` is AF when it has an increasing sequence of nonunital star
subalgebras indexed by `ℕ`, each closed and finite-dimensional over `ℂ`, whose
union is dense in the norm topology of `A`.

Source: G. J. Murphy, *C*-Algebras and Operator Theory*, Section 6.2. -/
def IsAF (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∃ stage : ℕ → NonUnitalStarSubalgebra ℂ A,
    Monotone stage ∧
      (∀ n, IsFiniteDimensionalSubalgebra (stage n)) ∧
      closure (⋃ n, (stage n : Set A)) = Set.univ

/-- **Finite-dimensional range of a star homomorphism.** If `D` and `A` are nonunital complex
C*-algebras, `D` is finite-dimensional over `ℂ`, and `f : D → A` is a nonunital star-algebra
homomorphism, its range is a closed finite-dimensional nonunital star subalgebra of `A`. The zero
homomorphism is included. -/
theorem isFiniteDimensionalSubalgebra_range
    {D : Type v} [NonUnitalCStarAlgebra D] [FiniteDimensional ℂ D]
    {A : Type u} [NonUnitalCStarAlgebra A] (f : D →⋆ₙₐ[ℂ] A) :
    IsFiniteDimensionalSubalgebra f.range := by
  let L : D →ₗ[ℂ] f.range :=
    { toFun := fun d => ⟨f d, f.mem_range_self d⟩
      map_add' := fun x y => Subtype.ext (map_add f x y)
      map_smul' := fun c x => Subtype.ext (map_smul f c x) }
  have hL : Function.Surjective L := by
    rintro ⟨a, ha⟩
    obtain ⟨d, hd⟩ := f.mem_range.mp ha
    exact ⟨d, Subtype.ext hd⟩
  letI : FiniteDimensional ℂ f.range := Module.Finite.of_surjective L hL
  refine ⟨?_, inferInstance⟩
  change IsClosed (f.range.toSubmodule : Set A)
  exact Submodule.closed_of_finiteDimensional _

/-- **AF algebras from increasing finite-dimensional ranges.** Let `A` be a nonunital complex
C*-algebra, let `Dₙ` be finite-dimensional nonunital complex C*-algebras, and let `fₙ : Dₙ → A` be
nonunital star-algebra homomorphisms. If their ranges increase with `n ∈ ℕ` and their union is
norm-dense in `A`, then `A` is approximately finite-dimensional. -/
theorem isAF_of_monotone_dense_range
    {A : Type u} [NonUnitalCStarAlgebra A]
    {D : ℕ → Type v} [∀ n, NonUnitalCStarAlgebra (D n)]
    [∀ n, FiniteDimensional ℂ (D n)]
    (f : ∀ n, D n →⋆ₙₐ[ℂ] A)
    (hmono : Monotone fun n => (f n).range)
    (hdense : Dense (⋃ n, Set.range (f n))) : IsAF A := by
  refine ⟨fun n => (f n).range, hmono,
    fun n => isFiniteDimensionalSubalgebra_range (f n), ?_⟩
  simpa only [NonUnitalStarAlgHom.coe_range] using hdense.closure_eq

/-- **Finite-dimensional C*-algebras are AF.** Every finite-dimensional nonunital complex C*-algebra is
approximately finite-dimensional, using the constant sequence of the whole algebra. This includes
the zero algebra. -/
theorem isAF_of_finiteDimensional
    (A : Type u) [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] : IsAF A := by
  apply isAF_of_monotone_dense_range (D := fun _ => A)
    (fun _ => NonUnitalStarAlgHom.id ℂ A) monotone_const
  change Dense (⋃ _ : ℕ, Set.range (id : A → A))
  simpa only [Set.range_id, Set.iUnion_const] using (dense_univ : Dense (Set.univ : Set A))

end CStarAlgebra
