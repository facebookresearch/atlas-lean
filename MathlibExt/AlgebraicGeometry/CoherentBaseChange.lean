/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from:

`Definitions/Def_AlgebraicGeometry_CoherentBaseChange.lean`,
`Definitions/Def_AlgebraicGeometry_CoherentBaseChangeFamily.lean`
and
`Definitions/Def_AlgebraicGeometry_MumfordTruncation.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
No individual authors are identified for these source files in the upstream
ATTRIBUTION.md.
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework. This module merges the three source files and adds docstrings. It
keeps their declaration names, statements and proofs, except that it does not
export the membership lemmas `mem_K0_iff`, which are `LinearMap.mem_ker` with
`LinearMap.coprod_apply`, or the negation maps `ι1`: the squares `comm` are
stated with `-g` and `-lift d`. Nor does it keep the source's construction of
`kerBaseChangeHom`: it is Mathlib's `LinearMap.tensorKer A A G.d`, with the
source's type, and the source's `kerBaseChangeHom_apply_coe` is Mathlib's
`LinearMap.tensorKer_coe`. The examples of the source's `Gates` section are
in the test module.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u v w w'

namespace CoherentBaseChange

/-- A two-term complex of finite free modules over a commutative ring,
given by a single differential `d : C0 →ₗ[R] C1`. -/
structure TwoTermComplex (R : Type u) [CommRing R] where
  C0 : Type v
  [C0_addCommGroup : AddCommGroup C0]
  [C0_module : Module R C0]
  [C0_finite : Module.Finite R C0]
  [C0_free : Module.Free R C0]
  C1 : Type v
  [C1_addCommGroup : AddCommGroup C1]
  [C1_module : Module R C1]
  [C1_finite : Module.Finite R C1]
  [C1_free : Module.Free R C1]
  d : C0 →ₗ[R] C1

attribute [instance] TwoTermComplex.C0_addCommGroup TwoTermComplex.C0_module
  TwoTermComplex.C0_finite TwoTermComplex.C0_free TwoTermComplex.C1_addCommGroup
  TwoTermComplex.C1_module TwoTermComplex.C1_finite TwoTermComplex.C1_free

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

/-- The dimension of the zeroth cohomology of the fibre of `G` at a prime. -/
def fibreH0 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    (LinearMap.ker (G.d.baseChange 𝔭.asIdeal.ResidueField))

/-- The dimension of the first cohomology of the fibre of `G` at a prime. -/
def fibreH1 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    ((𝔭.asIdeal.ResidueField ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange 𝔭.asIdeal.ResidueField))

/-- The Euler characteristic of `G`, as the alternating difference of ranks. -/
def chi : ℤ :=
  (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)

/-- The zeroth cohomology of `G` after base change to an `R`-algebra `A`,
realised as the kernel of the base-changed differential. -/
abbrev H0 (A : Type w) [CommRing A] [Algebra R A] : Submodule A (A ⊗[R] G.C0) :=
  LinearMap.ker (G.d.baseChange A)

/-- The comparison map from the base change of `ker d` to the kernel of
the base-changed differential. It is Mathlib's `LinearMap.tensorKer A A G.d`, whose coercion
lemma is `LinearMap.tensorKer_coe`. -/
abbrev kerBaseChangeHom (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker G.d) →ₗ[A] G.H0 A :=
  LinearMap.tensorKer A A G.d

end TwoTermComplex

/-- A family of two-term complexes over the affine opens of a scheme,
together with the function recording the fibre `H0` dimension at each
point and the compatibility of that function with the local complexes. -/
structure FibreH0Family (T : Scheme.{u}) where
  G : ∀ (U : T.Opens), IsAffineOpen U → TwoTermComplex.{u, u} Γ(T, U)
  h0 : T → ℕ
  hglue : ∀ (U : T.Opens) (hU : IsAffineOpen U) (t : U),
    h0 t = (G U hU).fibreH0 (hU.primeIdealOf t)

end CoherentBaseChange

namespace TwoChartCech

namespace KerCoprod

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0]
  [AddCommGroup C1] [Module R C1]
variable {P : Type w'} [AddCommGroup P] [Module R P]
variable (d : C0 →ₗ[R] C1) (g : P →ₗ[R] C1)

/-- The kernel of the coproduct map `d ⊕ g : C0 × P → C1`, the truncated
degree-zero term in a two-chart construction. -/
abbrev K0 : Submodule R (C0 × P) := LinearMap.ker (d.coprod g)

/-- The projection from `K0` to the second factor `P`. -/
def dK : K0 d g →ₗ[R] P := (LinearMap.snd R C0 P) ∘ₗ (K0 d g).subtype

/-- The projection from `K0` to the first factor `C0`. -/
def ι0 : K0 d g →ₗ[R] C0 := (LinearMap.fst R C0 P) ∘ₗ (K0 d g).subtype

@[simp] theorem dK_apply (z : K0 d g) : dK d g z = (z : C0 × P).2 := rfl
@[simp] theorem ι0_apply (z : K0 d g) : ι0 d g z = (z : C0 × P).1 := rfl

theorem comm : d ∘ₗ ι0 d g = (-g) ∘ₗ dK d g := by
  ext z
  have hz : d (z : C0 × P).1 + g (z : C0 × P).2 = 0 :=
    (LinearMap.coprod_apply d g _).symm.trans (LinearMap.mem_ker.mp z.2)
  simp only [LinearMap.comp_apply, ι0_apply, dK_apply, LinearMap.neg_apply,
    eq_neg_iff_add_eq_zero]
  exact hz

theorem ι0_prod_dK : (ι0 d g).prod (dK d g) = (K0 d g).subtype := by
  ext z <;> rfl

end KerCoprod

namespace Mumford

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0]
  [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

/-- The number of free generators used to present the cokernel of `d`. -/
def rank : ℕ := (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose

/-- A surjection from a finite free module onto the cokernel of `d`. -/
def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

theorem quot_surjective : Function.Surjective (quot d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose_spec

/-- A lift of `quot` to `C1`, using projectivity of the free module. -/
def lift : (Fin (rank d) → R) →ₗ[R] C1 :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose

theorem mkQ_comp_lift : (LinearMap.range d).mkQ ∘ₗ lift d = quot d :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose_spec

theorem mkQ_lift_apply (v : Fin (rank d) → R) :
    (LinearMap.range d).mkQ (lift d v) = quot d v := by
  rw [← LinearMap.comp_apply, mkQ_comp_lift]

theorem surjective_coprod : Function.Surjective (d.coprod (lift d)) := by
  intro y
  obtain ⟨v, hv⟩ := quot_surjective d ((LinearMap.range d).mkQ y)
  have hy : y - lift d v ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hv,
      mkQ_lift_apply, sub_self]
  obtain ⟨x, hx⟩ := hy
  exact ⟨(x, v), by simp only [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

/-- Mumford's truncated degree-zero term: the kernel of `d ⊕ lift`. -/
abbrev K0 : Submodule R (C0 × (Fin (rank d) → R)) := KerCoprod.K0 d (lift d)

/-- The projection from Mumford's `K0` to the free module. -/
abbrev dK : K0 d →ₗ[R] (Fin (rank d) → R) := KerCoprod.dK d (lift d)

/-- The projection from Mumford's `K0` to `C0`. -/
abbrev ι0 : K0 d →ₗ[R] C0 := KerCoprod.ι0 d (lift d)

@[simp] theorem dK_apply (z : K0 d) :
    dK d z = (z : C0 × (Fin (rank d) → R)).2 := rfl
@[simp] theorem ι0_apply (z : K0 d) :
    ι0 d z = (z : C0 × (Fin (rank d) → R)).1 := rfl

theorem comm : d ∘ₗ ι0 d = (-lift d) ∘ₗ dK d := KerCoprod.comm d (lift d)

theorem ι0_prod_dK : (ι0 d).prod (dK d) = (K0 d).subtype :=
  KerCoprod.ι0_prod_dK d (lift d)

end Mumford

end TwoChartCech

end
