/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplex
public import MathlibExt.LinearAlgebra.ExteriorPower.Semilinear
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

/-!
# Koszul maps along a scalar homomorphism

An actual semilinear map intertwining two coefficient functionals induces
exterior maps commuting with all Koszul differentials. With a common ground
ring, these are literal chain maps between the scalar-restricted complexes.
No resolution or homology-comparison assertion is an input.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe uR uS uM uN uk

namespace KoszulComplex

section Differential

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module S N]

/-- The original signed Koszul differentials commute with exterior powers
of an actual semilinear map preserving the coefficient functional. -/
theorem differential_semilinear
    (φ : R →+* S) (x : M →ₗ[R] R) (y : N →ₗ[S] S)
    (f : M →ₛₗ[φ] N) (hf : ∀ m, y (f m) = φ (x m)) (n : ℕ) :
    (exteriorPower.mapSemilinear φ f n).comp (differential R M x n) =
      (differential S N y n).comp (exteriorPower.mapSemilinear φ f (n + 1)) := by
  letI : Module R (⋀[S]^n N) := Module.compHom (⋀[S]^n N) φ
  let l := (exteriorPower.mapSemilinear φ f n).comp (differential R M x n)
  let r := (differential S N y n).comp (exteriorPower.mapSemilinear φ f (n + 1))
  let L : (⋀[R]^(n + 1) M) →ₗ[R] (⋀[S]^n N) :=
    { toFun := fun z => l z
      map_add' := fun z z' => l.map_add z z'
      map_smul' := fun a z => l.map_smulₛₗ a z }
  let T : (⋀[R]^(n + 1) M) →ₗ[R] (⋀[S]^n N) :=
    { toFun := fun z => r z
      map_add' := fun z z' => r.map_add z z'
      map_smul' := fun a z => r.map_smulₛₗ a z }
  have hLT : L = T := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change exteriorPower.mapSemilinear φ f n
      (differential R M x n (exteriorPower.ιMulti R (n + 1) a)) =
        differential S N y n
          (exteriorPower.mapSemilinear φ f (n + 1)
            (exteriorPower.ιMulti R (n + 1) a))
    rw [differential_apply_ιMulti, map_sum,
      exteriorPower.mapSemilinear_ιMulti, differential_apply_ιMulti]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smulₛₗ, exteriorPower.mapSemilinear_ιMulti,
      map_pow, map_neg, map_one, hf, Function.comp_def]
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun hLT z

end Differential

section Ground

variable (k : Type uk) [CommRing k]
  {R S : Type uR} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  {M N : Type uM} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]

/-- The actual semilinear exterior map is ground-linear for the native
scalar restrictions, using the algebra homomorphism's scalar law. -/
def semilinearGroundLevel (φ : R →ₐ[k] S) (f : M →ₛₗ[φ.toRingHom] N) (n : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R (⋀[R]^n M))) ⟶
      ((ModuleCat.restrictScalars (algebraMap k S)).obj (ModuleCat.of S (⋀[S]^n N))) :=
  by
    let X := (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R (⋀[R]^n M))
    let Y := (ModuleCat.restrictScalars (algebraMap k S)).obj (ModuleCat.of S (⋀[S]^n N))
    let l := exteriorPower.mapSemilinear φ.toRingHom f n
    let L : X →ₗ[k] Y :=
      { toFun := fun z => l z
        map_add' := fun z z' => l.map_add z z'
        map_smul' := by
          intro c z
          have h := l.map_smulₛₗ (algebraMap k R c) z
          have hc : φ.toRingHom (algebraMap k R c) = algebraMap k S c := φ.commutes c
          exact h.trans (congrArg (fun a => a • l z) hc) }
    exact ModuleCat.ofHom (R := k) (X := X) (Y := Y) L

/-- Literal scalar-restricted Koszul chain map induced by the original
semilinear generator map, with the actual exterior map in every degree. -/
def semilinearMap (φ : R →ₐ[k] S)
    (x : M →ₗ[R] R) (y : N →ₗ[S] S) (f : M →ₛₗ[φ.toRingHom] N)
    (hf : ∀ m, y (f m) = φ (x m)) :
    ((ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex (.down ℕ)).obj
        (complex R M x) ⟶
      ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.down ℕ)).obj
        (complex S N y) :=
  ChainComplex.ofHom (fun n => semilinearGroundLevel k φ f n) (by
    intro n
    change semilinearGroundLevel k φ f (n + 1) ≫
      (ModuleCat.restrictScalars (algebraMap k S)).map ((complex S N y).d (n + 1) n) =
        (ModuleCat.restrictScalars (algebraMap k R)).map ((complex R M x).d (n + 1) n) ≫
          semilinearGroundLevel k φ f n
    rw [complex_d_succ, complex_d_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change differential S N y n (exteriorPower.mapSemilinear φ.toRingHom f (n + 1) z) =
      exteriorPower.mapSemilinear φ.toRingHom f n (differential R M x n z)
    exact (DFunLike.congr_fun (differential_semilinear φ.toRingHom x y f hf n) z).symm)

/-- The chain map retains the actual exterior component. -/
theorem semilinearMap_f_apply (φ : R →ₐ[k] S)
    (x : M →ₗ[R] R) (y : N →ₗ[S] S) (f : M →ₛₗ[φ.toRingHom] N)
    (hf : ∀ m, y (f m) = φ (x m)) (n : ℕ) (z : ⋀[R]^n M) :
    ((semilinearMap k φ x y f hf).f n).hom z =
      exteriorPower.mapSemilinear φ.toRingHom f n z := rfl

/-- Actual decomposable Koszul words keep all original generator images. -/
theorem semilinearMap_f_ιMulti (φ : R →ₐ[k] S)
    (x : M →ₗ[R] R) (y : N →ₗ[S] S) (f : M →ₛₗ[φ.toRingHom] N)
    (hf : ∀ m, y (f m) = φ (x m)) (n : ℕ) (a : Fin n → M) :
    ((semilinearMap k φ x y f hf).f n).hom (exteriorPower.ιMulti R n a) =
      exteriorPower.ιMulti S n (fun j => f (a j)) :=
  exteriorPower.mapSemilinear_ιMulti φ.toRingHom f n a

end Ground

end KoszulComplex
