/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.Alternating.RestrictScalars
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of semilinear maps

For a ring homomorphism `φ : R →+* S` between commutative rings and a `φ`-semilinear map `f :
M → N`, exterior powers give `Λ^n_R M →ₛₗ[φ] Λ^n_S N`, with `v_0 ∧ ⋯ ∧ v_(n-1) ↦ f(v_0) ∧ ⋯ ∧
f(v_(n-1))`.

The identity scalar homomorphism gives the linear exterior map, and composition uses the
composite scalar homomorphism. The empty wedge in degree zero is the unit.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section
noncomputable section

universe uR uS uM uN

namespace exteriorPower

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module S N]

/-- Let `R,S` be commutative rings, `M` an `R`-module, `N` an `S`-module, `φ : R →+* S`, and `f :
M →ₛₗ[φ] N`. For every `n : ℕ`, `mapSemilinear φ f n : Λ^n_R M →ₛₗ[φ] Λ^n_S N` sends
`ιMulti_R(v)` to `ιMulti_S(f ∘ v)`. -/
def mapSemilinear (φ : R →+* S) (f : M →ₛₗ[φ] N) (n : ℕ) :
    (⋀[R]^n M) →ₛₗ[φ] (⋀[S]^n N) := by
  letI : Module R N := Module.compHom N φ
  letI : Module R (⋀[S]^n N) := Module.compHom (⋀[S]^n N) φ
  let fR : M →ₗ[R] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smulₛₗ }
  let aS : N [⋀^Fin n]→ₗ[S] (⋀[S]^n N) := exteriorPower.ιMulti S n
  let aR : N [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
    { toFun := aS
      map_update_add' := aS.map_update_add'
      map_update_smul' := fun v i r x => aS.map_update_smul' v i (φ r) x
      map_eq_zero_of_eq' := aS.map_eq_zero_of_eq' }
  let F : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) :=
    exteriorPower.alternatingMapLinearEquiv (aR.compLinearMap fR)
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' := F.map_smul }

/-- Let `R,S` be commutative rings, `M` an `R`-module, `N` an `S`-module, `φ : R →+* S`, and `f :
M →ₛₗ[φ] N`. For `n : ℕ` and `a : Fin n → M`, `mapSemilinear φ f n (ιMulti_R(a)) =
ιMulti_S(fun j ↦ f(a j))`, including the unit word in degree zero. -/
theorem mapSemilinear_ιMulti
    (φ : R →+* S) (f : M →ₛₗ[φ] N) (n : ℕ) (a : Fin n → M) :
    mapSemilinear φ f n (exteriorPower.ιMulti R n a) =
      exteriorPower.ιMulti S n (fun j => f (a j)) := by
  let : Module R N := Module.compHom N φ
  let : Module R (⋀[S]^n N) := Module.compHom (⋀[S]^n N) φ
  let fR : M →ₗ[R] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smulₛₗ }
  let aS : N [⋀^Fin n]→ₗ[S] (⋀[S]^n N) := exteriorPower.ιMulti S n
  let aR : N [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
    { toFun := aS
      map_update_add' := aS.map_update_add'
      map_update_smul' := fun v i r x => aS.map_update_smul' v i (φ r) x
      map_eq_zero_of_eq' := aS.map_eq_zero_of_eq' }
  change exteriorPower.alternatingMapLinearEquiv (aR.compLinearMap fR)
      (exteriorPower.ιMulti R n a) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- For a commutative ring `R`, an `R`-module `M`, an endomorphism `f : M →ₗ[R] M`, and `n : ℕ`,
`mapSemilinear (RingHom.id R) f n = exteriorPower.map n f`. -/
theorem mapSemilinear_id_scalar (f : M →ₗ[R] M) (n : ℕ) :
    mapSemilinear (RingHom.id R) f n = exteriorPower.map n f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  simp only [LinearMap.compAlternatingMap_apply, mapSemilinear_ιMulti,
    exteriorPower.map_apply_ιMulti, Function.comp_def]

/-- Let `R,S,T` be commutative rings, `M,N,P` respectively modules over them, `φ : R →+* S`, `ψ :
S →+* T`, `f : M →ₛₗ[φ] N`, and `g : N →ₛₗ[ψ] P`. With composite scalar map `ψ.comp φ` and its
`RingHomCompTriple` compatibility, `(mapSemilinear ψ g n).comp (mapSemilinear φ f n) =
mapSemilinear (ψ.comp φ) (g.comp f) n` for every `n : ℕ`. -/
theorem mapSemilinear_comp
    {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P] [Module T P]
    (φ : R →+* S) (ψ : S →+* T)
    (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P) (n : ℕ)
    [RingHomCompTriple φ ψ (ψ.comp φ)] :
    (mapSemilinear ψ g n).comp (mapSemilinear φ f n) =
      mapSemilinear (ψ.comp φ) (g.comp f) n := by
  let : Algebra R T := (ψ.comp φ).toAlgebra
  let : Module R (⋀[T]^n P) := Module.compHom (⋀[T]^n P) (ψ.comp φ)
  let lhs : (⋀[R]^n M) →ₗ[R] (⋀[T]^n P) :=
    { toFun := (mapSemilinear ψ g n).comp (mapSemilinear φ f n)
      map_add' := map_add _
      map_smul' := ((mapSemilinear ψ g n).comp (mapSemilinear φ f n)).map_smulₛₗ }
  let rhs : (⋀[R]^n M) →ₗ[R] (⋀[T]^n P) :=
    { toFun := mapSemilinear (ψ.comp φ) (g.comp f) n
      map_add' := (mapSemilinear (ψ.comp φ) (g.comp f) n).map_add
      map_smul' := (mapSemilinear (ψ.comp φ) (g.comp f) n).map_smulₛₗ }
  have h : lhs = rhs := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change mapSemilinear ψ g n
        (mapSemilinear φ f n (exteriorPower.ιMulti R n a)) =
      mapSemilinear (ψ.comp φ) (g.comp f) n (exteriorPower.ιMulti R n a)
    rw [mapSemilinear_ιMulti, mapSemilinear_ιMulti, mapSemilinear_ιMulti]
    rfl
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun h x

end exteriorPower
