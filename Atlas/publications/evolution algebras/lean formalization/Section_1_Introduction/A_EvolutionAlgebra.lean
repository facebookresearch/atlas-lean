/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Section 1: evolution algebras — definitions

Core definitions for finite-dimensional evolution algebras, following the
paper (`evolution_algebras.pdf`, Preliminaries).

An **evolution algebra** over a field `K` is a (non-associative) `K`-algebra
with a distinguished basis `B`, the **natural basis**, such that
`x * y = 0` for distinct `x, y ∈ B`. The algebra is referenced on its own;
the natural basis and the structure matrix are accessed through
`EvolutionAlgebra.natural_basis` and `EvolutionAlgebra.struct_matrix`.

Mathlib has no `NonUnitalNonAssocAlgebra` class: the Mathlib idiom is the
unbundled `[CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
[IsScalarTower R A A] [SMulCommClass R A A]`
(cf. `Mathlib/Algebra/FreeNonUnitalNonAssocAlgebra.lean`). We package that
bundle as one class so general statements take a single hypothesis;
parent projections recover the components.

## Main definitions

* `NonUnitalNonAssocAlgebra`: a non-unital non-associative algebra over a
  semiring, packaging `Module` with scalar–multiplication compatibility.
* `EvolutionAlgebra`: an evolution algebra, as a `Prop`-valued class recording
  the existence of a natural basis (cf. Mathlib's `FiniteDimensional`).
* `EvolutionAlgebra.exists_orthogonal_basis`: the underlying existence statement.
* `EvolutionAlgebra.natural_basis`: a chosen natural basis (noncomputable).
* `EvolutionAlgebra.struct_matrix`: the structure matrix w.r.t. a natural basis.
-/

universe u v

/-- **Helper.** A non-unital, non-associative algebra over a semiring `R`: a
`NonUnitalNonAssocSemiring` with a compatible scalar action. This packages
the Mathlib bundle (`Module` + `IsScalarTower` + `SMulCommClass`) as one
class so general statements take a single hypothesis; the parent
projections recover the components. It cannot be `Prop`-valued since
`Module` is not a `Prop`. Each concrete algebra declares how it satisfies
this bundle once its component structures are in place (see the instance
for `Counterexample`). -/
class NonUnitalNonAssocAlgebra (R A : Type*) [CommSemiring R]
    [NonUnitalNonAssocSemiring A]
  extends Module R A, IsScalarTower R A A, SMulCommClass R A A

/-- **Section 1.** A finite-dimensional evolution algebra over a field `K`: a non-unital
non-associative `K`-algebra possessing a natural basis, i.e. a basis
`B = {e₁, …, eₙ}` with `eᵢ * eⱼ = 0` for `i ≠ j` (Section 2, Preliminaries).
The basis is not part of the signature; use
`EvolutionAlgebra.natural_basis` to access one. This class is the hypothesis
of C1's `Conjecture`. -/
class EvolutionAlgebra (K : Type u) (E : Type v) [Field K] [NonUnitalNonAssocSemiring E]
    [NonUnitalNonAssocAlgebra K E] : Prop where
  exists_natural_basis : ∃ (n : ℕ) (b : Module.Basis (Fin n) K E),
    ∀ i j : Fin n, i ≠ j → b i * b j = 0

namespace EvolutionAlgebra

variable (K : Type u) (E : Type v) [Field K] [NonUnitalNonAssocSemiring E]
  [NonUnitalNonAssocAlgebra K E]

/-- The existence statement behind `natural_basis`: some finite basis of `E`
is pairwise orthogonal. This is the class field, restated for direct use. -/
theorem exists_orthogonal_basis [self : EvolutionAlgebra K E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K E),
      ∀ i j : Fin n, i ≠ j → b i * b j = 0 :=
  self.exists_natural_basis

/-- A chosen natural basis of the evolution algebra `E`, as a dependent pair
of the dimension and the basis. Noncomputable: chosen from
`exists_natural_basis`. Accessor for the basis the class records. -/
noncomputable def natural_basis [self : EvolutionAlgebra K E] :
    Σ' (n : ℕ), Module.Basis (Fin n) K E :=
  have h := Classical.indefiniteDescription _ self.exists_natural_basis
  ⟨h.val, Classical.indefiniteDescription _ h.property |>.val⟩

/-- The structure matrix of `E` with respect to a natural basis `b`: the
`(i, j)`-entry is the `j`-th coordinate of `b i * b i`, i.e.
`eᵢ * eᵢ = ∑ j, M i j • eⱼ` (Section 2: `M_B(𝓔)`). Accessor for structure
constants. -/
noncomputable def struct_matrix (n : ℕ) (b : Module.Basis (Fin n) K E) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => b.repr (b i * b i) j

end EvolutionAlgebra
