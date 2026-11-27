/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/LinearAlgebra/TensorAlgebra/SemilinearMap.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: retain only the exterior-algebra and exterior-power base change and its
functoriality; omit the tensor-algebra and target-ring lifting portions.
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Semilinear base change of exterior algebras and exterior powers

A ring homomorphism `φ : R →+* S` and a `φ`-semilinear map `u : M →ₛₗ[φ] N` induce a ring
homomorphism `ExteriorAlgebra.mapₛₗ φ u : ExteriorAlgebra R M →+* ExteriorAlgebra S N` with
`ι R m ↦ ι S (u m)`, constructed from the universal property of the exterior algebra. It maps
`⋀[R]^n M` into `⋀[S]^n N`, giving `φ`-semilinear maps `ExteriorAlgebra.powMapₛₗ n φ u`, which
are compatible with identities and composition.
-/

@[expose] public noncomputable section

/-- A ring homomorphism carrying the `i`-th factors of an ordered product to
those of another
carries the product to the product. -/
private theorem map_ofFn_prod {A B : Type*} [Semiring A] [Semiring B] (f : A
  →+* B) {n : ℕ}
    (a : Fin n → A) (b : Fin n → B) (h : ∀ i, f (a i) = b i) :
    f (List.ofFn a).prod = (List.ofFn b).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, h]

/-- A ring homomorphism compatible with scalars and generators carries the
`n`-th power of the
range of one generator map into that of the other. -/
private theorem map_mem_pow_range {R S M N A B : Type*} [CommSemiring R]
  [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [Semiring A]
      [Semiring B]
    [Algebra R A] [Algebra S B] (ιA : M →ₗ[R] A) (ιB : N →ₗ[S] B) (f : A →+* B)
      (φ : R →+* S)
    (u : M →ₛₗ[φ] N) (h₀ : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (h₁ : ∀ m, f (ιA m) = ιB (u m)) (n : ℕ) {x : A} (hx : x ∈ LinearMap.range
      ιA ^ n) :
    f x ∈ LinearMap.range ιB ^ n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [h₀, pow_zero]; exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x _ ih =>
      obtain ⟨m₀, rfl⟩ := hm
      rw [map_mul, h₁, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (u m₀)) ih

namespace ExteriorAlgebra

/-! ### Base change of the exterior algebra -/

section BaseChange

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N]
    [Module S N]

/-- `ExteriorAlgebra S N` viewed as an `R`-algebra by restricting scalars along
a ring
homomorphism `φ : R →+* S`. -/
@[instance_reducible]
noncomputable def algebraOfRingHom (φ : R →+* S) : Algebra R (ExteriorAlgebra S
  N) :=
  ((algebraMap S (ExteriorAlgebra S N)).comp φ).toAlgebra' fun c x =>
    Algebra.commutes (φ c) x

/-- The degree-one generator of `ExteriorAlgebra S N`, read along a semilinear
map
`u : M →ₛₗ[φ] N` as an `R`-linear map on `M`, where `R` acts through `φ`. -/
noncomputable def ιCompₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    letI := algebraOfRingHom (N := N) φ
    M →ₗ[R] ExteriorAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  { toFun := fun m => ExteriorAlgebra.ι S (u m)
    map_add' := fun m m' => by rw [map_add, map_add]
    map_smul' := fun r m => by
      change ExteriorAlgebra.ι S (u (r • m)) = r • ExteriorAlgebra.ι S (u m)
      rw [map_smulₛₗ, map_smul, Algebra.smul_def, Algebra.smul_def]
      rfl }

/-- Every value of `ιCompₛₗ` squares to zero. -/
theorem ιCompₛₗ_sq_zero (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    letI := algebraOfRingHom (N := N) φ
    ιCompₛₗ φ u m * ιCompₛₗ φ u m = 0 :=
  ExteriorAlgebra.ι_sq_zero (u m)

/-- A ring homomorphism `φ : R →+* S` together with a
`φ`-semilinear map `u : M →ₛₗ[φ] N` induces a ring homomorphism
`ExteriorAlgebra R M →+* ExteriorAlgebra S N` carrying `ι R m` to `ι S (u m)`.
-/
noncomputable def mapₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    ExteriorAlgebra R M →+* ExteriorAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  (ExteriorAlgebra.lift R
    ⟨ιCompₛₗ φ u, fun m => ExteriorAlgebra.ι_sq_zero (u m)⟩).toRingHom

/-- Base change carries the generator `ι R m` to `ι S (u m)`. -/
@[simp]
theorem mapₛₗ_ι (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    mapₛₗ φ u (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (u m) :=
  let := algebraOfRingHom (N := N) φ
  ExteriorAlgebra.lift_ι_apply R (ιCompₛₗ φ u) (fun m =>
    ExteriorAlgebra.ι_sq_zero (u m)) m

/-- Base change carries the wedge `ιMulti R n v` of a family of vectors to the
wedge of their
images. -/
theorem mapₛₗ_ιMulti (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ) (v : Fin n → M) :
    mapₛₗ φ u (ιMulti R n v) = ιMulti S n fun i => u (v i) := by
  rw [ιMulti_apply, ιMulti_apply]
  exact map_ofFn_prod _ _ _ fun i => mapₛₗ_ι φ u _

/-- Base change carries the scalar `r` to the scalar `φ r`. -/
@[simp]
theorem mapₛₗ_algebraMap (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) :
    mapₛₗ φ u (algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap S (ExteriorAlgebra S N) (φ r) :=
  let := algebraOfRingHom (N := N) φ
  (ExteriorAlgebra.lift R
    ⟨ιCompₛₗ φ u, fun m => ExteriorAlgebra.ι_sq_zero (u m)⟩).commutes r

/-- Two ring homomorphisms out of an exterior algebra agree as soon as they
agree on the image
of the base ring and on the degree-one generators. -/
theorem ringHom_ext {T : Type*} [Semiring T] {f g : ExteriorAlgebra R M →+* T}
    (h₁ : ∀ r : R, f (algebraMap R (ExteriorAlgebra R M) r) =
      g (algebraMap R (ExteriorAlgebra R M) r))
    (h₂ : ∀ m : M, f (ExteriorAlgebra.ι R m) = g (ExteriorAlgebra.ι R m)) : f =
      g := by
  refine RingHom.ext fun x => ?_
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact h₁ r
  | ι m => exact h₂ m
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Base change is semilinear along `φ`. -/
theorem mapₛₗ_smul (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) (x : ExteriorAlgebra
  R M) :
    mapₛₗ φ u (r • x) = φ r • mapₛₗ φ u x := by
  rw [Algebra.smul_def, map_mul, mapₛₗ_algebraMap, Algebra.smul_def]

/-- Base change along `χ = ψ ∘ φ` and `v = w ∘ u` is the composite of the base
changes along
`φ, u` and `ψ, w`. -/
theorem mapₛₗ_eq_comp {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P]
  [Module T P]
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] P)
    (v : M →ₛₗ[χ] P) (hχ : ∀ r, χ r = ψ (φ r)) (hv : ∀ m, v m = w (u m))
    (x : ExteriorAlgebra R M) : mapₛₗ χ v x = mapₛₗ ψ w (mapₛₗ φ u x) :=
  RingHom.congr_fun (ringHom_ext (f := mapₛₗ χ v) (g := (mapₛₗ ψ w).comp (mapₛₗ
    φ u))
    (fun r => by simp [hχ]) fun m => by simp [hv]) x

/-- Base change along maps that are pointwise the identity is the identity. -/
theorem mapₛₗ_eq_self {φ : R →+* R} (u : M →ₛₗ[φ] M) (hφ : ∀ r, φ r = r) (hu :
  ∀ m, u m = m)
    (x : ExteriorAlgebra R M) : mapₛₗ φ u x = x :=
  RingHom.congr_fun (ringHom_ext (f := mapₛₗ φ u) (g := RingHom.id
    (ExteriorAlgebra R M))
    (fun r => by simp [hφ]) fun m => by simp [hu]) x

/-- Base change carries `⋀[R]^n M` into `⋀[S]^n N`. -/
theorem mapₛₗ_mem_exteriorPower (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) : mapₛₗ φ u x ∈ ⋀[S]^n N := by
  exact map_mem_pow_range _ _ (mapₛₗ φ u) φ u (mapₛₗ_algebraMap φ u) (mapₛₗ_ι φ
    u) n hx

/-- `1` lies in `⋀[R]^0 M`. -/
theorem one_mem_exteriorPower : (1 : ExteriorAlgebra R M) ∈ ⋀[R]^0 M := by
  rw [show (⋀[R]^0 M) = 1 from pow_zero _]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

/-- The generators lie in `⋀[R]^1 M`. -/
theorem ι_mem_exteriorPower (m : M) : ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [show (⋀[R]^1 M) = LinearMap.range (ExteriorAlgebra.ι R) from pow_one _]
  exact LinearMap.mem_range_self _ m

/-- `⋀[R]^i M` and `⋀[R]^j M` multiply into `⋀[R]^(i + j) M`. -/
theorem mul_mem_exteriorPower {i j : ℕ} {x y : ExteriorAlgebra R M} (hx : x ∈
  ⋀[R]^i M)
    (hy : y ∈ ⋀[R]^j M) : x * y ∈ ⋀[R]^(i + j) M := by
  rw [show (⋀[R]^(i + j) M) = (⋀[R]^i M) * (⋀[R]^j M) from pow_add _ i j]
  exact Submodule.mul_mem_mul hx hy

/-- The restriction of
`ExteriorAlgebra.mapₛₗ φ u` to the degree-`n` pieces, as a `φ`-semilinear map
`⋀[R]^n M →ₛₗ[φ] ⋀[S]^n N`. -/
noncomputable def powMapₛₗ (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    ⋀[R]^n M →ₛₗ[φ] ⋀[S]^n N where
  toFun x := ⟨mapₛₗ φ u x, mapₛₗ_mem_exteriorPower φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (mapₛₗ_smul φ u r x)

/-- The underlying element of `powMapₛₗ n φ u x` is `mapₛₗ φ u x`. -/
@[simp]
theorem powMapₛₗ_coe (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (x : ⋀[R]^n M) :
    (powMapₛₗ n φ u x : ExteriorAlgebra S N) = mapₛₗ φ u x := rfl

/-- Base change of the `n`-th exterior power carries a wedge to the wedge of
the images,
`u (v 0) ∧ ⋯ ∧ u (v (n-1))`. -/
@[simp]
theorem powMapₛₗ_ιMulti (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (v : Fin n → M) :
    powMapₛₗ n φ u (_root_.exteriorPower.ιMulti R n v) =
      _root_.exteriorPower.ιMulti S n fun i => u (v i) := by
  refine Subtype.ext ?_
  rw [powMapₛₗ_coe, _root_.exteriorPower.ιMulti_apply_coe,
    _root_.exteriorPower.ιMulti_apply_coe,
    mapₛₗ_ιMulti]

/-- Two semilinear maps out of `⋀[R]^n M` agreeing on the wedges of families of
vectors are
equal. -/
theorem powMapₛₗ_ext {P : Type*} [AddCommGroup P] [Module S P] {n : ℕ} {φ : R
  →+* S}
    {f g : (⋀[R]^n M) →ₛₗ[φ] P}
    (h : ∀ v : Fin n → M,
      f (_root_.exteriorPower.ιMulti R n v) = g (_root_.exteriorPower.ιMulti R
        n v)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ (⊤ : Submodule R (⋀[R]^n M)) := Submodule.mem_top
  rw [← _root_.exteriorPower.ιMulti_span R n M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨v, rfl⟩ := hy; exact h v
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- Base change of the `n`-th exterior power along `χ = ψ ∘ φ` and `v = w ∘ u`
is the composite
of the base changes along `φ, u` and `ψ, w`. -/
theorem powMapₛₗ_eq_comp {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P]
  [Module T P]
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (n : ℕ) (u : M →ₛₗ[φ] N) (w : N
      →ₛₗ[ψ] P)
    (v : M →ₛₗ[χ] P) (hχ : ∀ r, χ r = ψ (φ r)) (hv : ∀ m, v m = w (u m)) (x :
      ⋀[R]^n M) :
    powMapₛₗ n χ v x = powMapₛₗ n ψ w (powMapₛₗ n φ u x) :=
  Subtype.ext (mapₛₗ_eq_comp u w v hχ hv x)

/-- Base change of the `n`-th exterior power along maps that are pointwise the
identity is the
identity. -/
theorem powMapₛₗ_eq_self {φ : R →+* R} (n : ℕ) (u : M →ₛₗ[φ] M) (hφ : ∀ r, φ r
  = r)
    (hu : ∀ m, u m = m) (x : ⋀[R]^n M) : powMapₛₗ n φ u x = x :=
  Subtype.ext (mapₛₗ_eq_self u hφ hu x)

end BaseChange

end ExteriorAlgebra
