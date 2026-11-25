/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import MathlibExt.LinearAlgebra.TensorProduct.TwoDirectedSystems

/-!
# Positive tensor powers of directed module systems

For a directed system `G i`, this file equips every positive left-associated
tensor power of `G i` with its induced directed system.  Its direct limit is
canonically equivalent to the corresponding tensor power of `lim G`.
Consequently, an element of any positive tensor power that vanishes after
mapping to the direct limit already vanishes at one finite stage.

The positive power indexed by `n` has `n + 1` factors.  This convention
matches the positive tensor powers used by the arbitrary-weight Kummer cup
construction. The successor comparison uses the generalized simultaneous
tensor/direct-limit equivalence directly, keeping this same positive-power
carrier and its canonical stage maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Module Module.DirectLimit

namespace TensorProduct

universe u v w x y

variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]

/-- The left-associated tensor power with `n + 1` factors, bundled as an
`R`-module.  Bundling the recursion keeps the induced additive and module
structures canonical in every universe. -/
noncomputable def positiveTensorPowerModuleObj
    (M : Type w) [AddCommGroup M] [Module R M] :
    ℕ → ModuleCat.{max u w} R
  | 0 => ModuleCat.of R (R ⊗[R] M)
  | n + 1 => ModuleCat.of R
      ((positiveTensorPowerModuleObj M n : Type (max u w)) ⊗[R] M)

attribute [reducible] positiveTensorPowerModuleObj

/-- The carrier of the positive tensor-power module object. -/
abbrev positiveTensorPower (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type (max u w) :=
  positiveTensorPowerModuleObj (R := R) M n

/-- The zero-indexed positive power is the tensor unit tensored with the
base module. -/
noncomputable def positiveTensorPowerZeroEquiv
    (M : Type w) [AddCommGroup M] [Module R M] :
    positiveTensorPower (R := R) M 0 ≃ₗ[R] R ⊗[R] M := by
  with_reducible
    exact LinearEquiv.refl R _

/-- Splitting off the final factor of a positive tensor power. -/
noncomputable def positiveTensorPowerSuccEquiv
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ) :
    positiveTensorPower (R := R) M (n + 1) ≃ₗ[R]
      positiveTensorPower (R := R) M n ⊗[R] M := by
  with_reducible
    exact LinearEquiv.refl R _

@[simp]
theorem positiveTensorPowerZeroEquiv_apply
    (M : Type w) [AddCommGroup M] [Module R M]
    (x : positiveTensorPower (R := R) M 0) :
    positiveTensorPowerZeroEquiv M x = x :=
  rfl

@[simp]
theorem positiveTensorPowerZeroEquiv_symm_apply
    (M : Type w) [AddCommGroup M] [Module R M]
    (x : R ⊗[R] M) :
    (positiveTensorPowerZeroEquiv M).symm x = x :=
  rfl

@[simp]
theorem positiveTensorPowerSuccEquiv_apply
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ)
    (x : positiveTensorPower (R := R) M (n + 1)) :
    positiveTensorPowerSuccEquiv M n x = x :=
  rfl

@[simp]
theorem positiveTensorPowerSuccEquiv_symm_apply
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ)
    (x : positiveTensorPower (R := R) M n ⊗[R] M) :
    (positiveTensorPowerSuccEquiv M n).symm x = x :=
  rfl

/-- The map on a positive tensor power induced by a linear map. -/
noncomputable def positiveTensorPowerMap
    {M : Type w} {N : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : ∀ n : ℕ,
      positiveTensorPower (R := R) M n →ₗ[R]
        positiveTensorPower (R := R) N n
  | 0 => LinearMap.lTensor R f
  | n + 1 => TensorProduct.map (positiveTensorPowerMap f n) f

attribute [reducible] positiveTensorPowerMap

@[simp]
theorem positiveTensorPowerMap_zero
    {M : Type w} {N : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    positiveTensorPowerMap f 0 = LinearMap.lTensor R f :=
  rfl

@[simp]
theorem positiveTensorPowerMap_succ
    {M : Type w} {N : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    positiveTensorPowerMap f (n + 1) =
      TensorProduct.map (positiveTensorPowerMap f n) f :=
  rfl

/-- Positive tensor powers preserve identity linear maps. -/
@[simp]
theorem positiveTensorPowerMap_id
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ) :
    positiveTensorPowerMap (LinearMap.id (R := R) (M := M)) n =
      LinearMap.id := by
  induction n with
  | zero => exact LinearMap.lTensor_id (R := R) R M
  | succ n ih =>
      rw [positiveTensorPowerMap_succ, ih, TensorProduct.map_id]

/-- Positive tensor powers preserve composition of linear maps. -/
theorem positiveTensorPowerMap_comp
    {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    positiveTensorPowerMap (g.comp f) n =
      (positiveTensorPowerMap g n).comp
        (positiveTensorPowerMap f n) := by
  induction n with
  | zero => exact LinearMap.lTensor_comp (M := R) (f := f) (g := g)
  | succ n ih =>
      rw [positiveTensorPowerMap_succ, positiveTensorPowerMap_succ,
        positiveTensorPowerMap_succ, ih, TensorProduct.map_comp]

/-- A linear equivalence induces a linear equivalence on every positive
tensor power. -/
noncomputable def positiveTensorPowerCongr
    {M : Type w} {N : Type x}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) :
    positiveTensorPower (R := R) M n ≃ₗ[R]
      positiveTensorPower (R := R) N n :=
  LinearEquiv.ofLinearMap
    (positiveTensorPowerMap e.toLinearMap n)
    (positiveTensorPowerMap e.symm.toLinearMap n) (by
      apply LinearMap.ext
      intro z
      change positiveTensorPowerMap e.toLinearMap n
          (positiveTensorPowerMap e.symm.toLinearMap n z) = z
      rw [← LinearMap.comp_apply, ← positiveTensorPowerMap_comp]
      have hcomp : e.toLinearMap.comp e.symm.toLinearMap =
          LinearMap.id := by
        apply LinearMap.ext
        intro y
        exact e.apply_symm_apply y
      rw [hcomp, positiveTensorPowerMap_id, LinearMap.id_apply]) (by
      apply LinearMap.ext
      intro z
      change positiveTensorPowerMap e.symm.toLinearMap n
          (positiveTensorPowerMap e.toLinearMap n z) = z
      rw [← LinearMap.comp_apply, ← positiveTensorPowerMap_comp]
      have hcomp : e.symm.toLinearMap.comp e.toLinearMap =
          LinearMap.id := by
        apply LinearMap.ext
        intro y
        exact e.symm_apply_apply y
      rw [hcomp, positiveTensorPowerMap_id, LinearMap.id_apply])

@[simp]
theorem positiveTensorPowerCongr_apply
    {M : Type w} {N : Type x}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ)
    (x : positiveTensorPower (R := R) M n) :
    positiveTensorPowerCongr e n x =
      positiveTensorPowerMap e.toLinearMap n x :=
  rfl

/-- Naturality of the zero-indexed positive-power splitting. -/
theorem positiveTensorPowerZeroEquiv_naturality
    {M : Type w} {N : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    (positiveTensorPowerZeroEquiv N).toLinearMap.comp
        (positiveTensorPowerMap g 0) =
      (LinearMap.lTensor R g).comp
        (positiveTensorPowerZeroEquiv M).toLinearMap := by
  apply LinearMap.ext
  intro z
  rfl

/-- Naturality of splitting off the final positive tensor-power factor. -/
theorem positiveTensorPowerSuccEquiv_naturality
    {M : Type w} {N : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (n : ℕ) :
    (positiveTensorPowerSuccEquiv N n).toLinearMap.comp
        (positiveTensorPowerMap g (n + 1)) =
      (TensorProduct.map (positiveTensorPowerMap g n) g).comp
        (positiveTensorPowerSuccEquiv M n).toLinearMap := by
  apply LinearMap.ext
  intro z
  rfl

variable {G : ι → Type w}
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- The transition map on a positive tensor power of a directed system. -/
noncomputable def positiveTensorPowerTransition
    (n : ℕ) (i j : ι) (hij : i ≤ j) :
    positiveTensorPower (R := R) (G i) n →ₗ[R]
      positiveTensorPower (R := R) (G j) n :=
  positiveTensorPowerMap (f i j hij) n

attribute [reducible] positiveTensorPowerTransition

omit [DecidableEq ι] [IsDirectedOrder ι]
  [DirectedSystem G (f · · ·)] in
/-- Successor splitting is natural for the stagewise transition, stated
with the canonical diagonal transition on the target system. -/
theorem positiveTensorPowerSuccEquiv_transition_naturality
    (n : ℕ) (i j : ι) (hij : i ≤ j) :
    (positiveTensorPowerSuccEquiv (R := R) (G j) n).toLinearMap.comp
        (positiveTensorPowerTransition f (n + 1) i j hij) =
      (diagonalTransition
        (positiveTensorPowerTransition f n) f i j hij).comp
        (positiveTensorPowerSuccEquiv (R := R) (G i) n).toLinearMap := by
  simpa only [positiveTensorPowerTransition, diagonalTransition] using
    positiveTensorPowerSuccEquiv_naturality (f i j hij) n

/-- Every positive tensor power of a directed module system is again a
directed system. -/
instance positiveTensorPowerDirectedSystem (n : ℕ) :
    DirectedSystem
      (fun i => positiveTensorPower (R := R) (G i) n)
      (positiveTensorPowerTransition f n · · ·) where
  map_self i x := by
    have hself : f i i le_rfl = LinearMap.id := by
      apply LinearMap.ext
      intro y
      exact DirectedSystem.map_self' f y
    rw [positiveTensorPowerTransition, hself,
      positiveTensorPowerMap_id, LinearMap.id_apply]
  map_map {k j i} hij hjk x := by
    have hcomp : (f j k hjk).comp (f i j hij) =
        f i k (hij.trans hjk) := by
      apply LinearMap.ext
      intro y
      exact DirectedSystem.map_map' f hij hjk y
    change positiveTensorPowerMap (f j k hjk) n
        (positiveTensorPowerMap (f i j hij) n x) =
      positiveTensorPowerMap (f i k (hij.trans hjk)) n x
    rw [← LinearMap.comp_apply, ← positiveTensorPowerMap_comp, hcomp]

/-- The direct limit of the positive tensor-power system is the same tensor
power of the original direct limit. -/
noncomputable def positiveTensorPowerDirectLimitEquiv : ∀ n : ℕ,
    Module.DirectLimit
        (fun i => positiveTensorPower (R := R) (G i) n)
        (positiveTensorPowerTransition f n) ≃ₗ[R]
      positiveTensorPower (R := R) (Module.DirectLimit G f) n
  | 0 =>
      Module.DirectLimit.congr
          (fun i => positiveTensorPowerZeroEquiv (G i))
          (fun i j hij =>
            positiveTensorPowerZeroEquiv_naturality (f i j hij)) ≪≫ₗ
        (TensorProduct.directLimitRight f R).symm ≪≫ₗ
        (positiveTensorPowerZeroEquiv
          (Module.DirectLimit G f)).symm
  | n + 1 =>
      Module.DirectLimit.congr
          (fun i => positiveTensorPowerSuccEquiv (G i) n)
          (fun i j hij =>
            positiveTensorPowerSuccEquiv_naturality (f i j hij) n) ≪≫ₗ
        directLimitDiagonal
          (positiveTensorPowerTransition f n) f ≪≫ₗ
        TensorProduct.congr
          (positiveTensorPowerDirectLimitEquiv n)
          (LinearEquiv.refl R (Module.DirectLimit G f)) ≪≫ₗ
        (positiveTensorPowerSuccEquiv
          (Module.DirectLimit G f) n).symm

attribute [reducible] positiveTensorPowerDirectLimitEquiv

/-- The tensor-power direct-limit equivalence sends a stage representative
to the positive tensor power of the canonical stage map. -/
@[simp]
theorem positiveTensorPowerDirectLimitEquiv_apply_of :
    ∀ (n : ℕ) (i : ι)
      (x : positiveTensorPower (R := R) (G i) n),
      positiveTensorPowerDirectLimitEquiv f n
          (Module.DirectLimit.of R ι _
            (positiveTensorPowerTransition f n) i x) =
        positiveTensorPowerMap
          (Module.DirectLimit.of R ι G f i) n x
  | 0, i, x => by
      let stageEquiv := fun j =>
        positiveTensorPowerZeroEquiv (R := R) (G j)
      let stageCongr := Module.DirectLimit.congr stageEquiv
        (fun a b hab =>
          positiveTensorPowerZeroEquiv_naturality (f a b hab))
      calc
        positiveTensorPowerDirectLimitEquiv f 0
            (Module.DirectLimit.of R ι _
              (positiveTensorPowerTransition f 0) i x) =
          (positiveTensorPowerZeroEquiv (R := R)
              (Module.DirectLimit G f)).symm
            ((TensorProduct.directLimitRight f R).symm
              (stageCongr
                (Module.DirectLimit.of R ι _
                  (positiveTensorPowerTransition f 0) i x))) := rfl
        _ = (positiveTensorPowerZeroEquiv (R := R)
              (Module.DirectLimit G f)).symm
            ((TensorProduct.directLimitRight f R).symm
              (Module.DirectLimit.of R ι _
                (fun a b hab => LinearMap.lTensor R (f a b hab)) i
                (positiveTensorPowerZeroEquiv (R := R) (G i) x))) := by
              rw [Module.DirectLimit.congr_apply_of]
        _ = positiveTensorPowerMap
            (Module.DirectLimit.of R ι G f i) 0 x := by
              rw [positiveTensorPowerZeroEquiv_apply,
                positiveTensorPowerZeroEquiv_symm_apply,
                positiveTensorPowerMap_zero]
              induction x using TensorProduct.inductionOn with
              | tmul r y =>
                  rw [TensorProduct.directLimitRight_symm_of_tmul,
                    LinearMap.lTensor_tmul]
              | add x y hx hy => simp only [map_add, hx, hy]
  | n + 1, i, x => by
      let stageEquiv := fun j =>
        positiveTensorPowerSuccEquiv (R := R) (G j) n
      let stageCongr := Module.DirectLimit.congr
        (f' := diagonalTransition
          (positiveTensorPowerTransition f n) f) stageEquiv
        (fun a b hab =>
          positiveTensorPowerSuccEquiv_transition_naturality
            f n a b hab)
      let diagonalEquiv := directLimitDiagonal
        (positiveTensorPowerTransition f n) f
      let factorEquiv := TensorProduct.congr
        (positiveTensorPowerDirectLimitEquiv f n)
        (LinearEquiv.refl R (Module.DirectLimit G f))
      calc
        positiveTensorPowerDirectLimitEquiv f (n + 1)
            (Module.DirectLimit.of R ι _
              (positiveTensorPowerTransition f (n + 1)) i x) =
          (positiveTensorPowerSuccEquiv (R := R)
              (Module.DirectLimit G f) n).symm
            (factorEquiv
              (diagonalEquiv
                (stageCongr
                  (Module.DirectLimit.of R ι _
                    (positiveTensorPowerTransition f (n + 1)) i x)))) := rfl
        _ = (positiveTensorPowerSuccEquiv (R := R)
              (Module.DirectLimit G f) n).symm
            (factorEquiv
              (diagonalEquiv
                (Module.DirectLimit.of R ι _
                  (diagonalTransition
                    (positiveTensorPowerTransition f n) f) i
                  (positiveTensorPowerSuccEquiv (R := R) (G i) n x)))) := by
              dsimp only [stageCongr]
              rw [Module.DirectLimit.congr_apply_of]
        _ = (positiveTensorPowerSuccEquiv (R := R)
              (Module.DirectLimit G f) n).symm
            (factorEquiv
              (TensorProduct.map
                (Module.DirectLimit.of R ι _
                  (positiveTensorPowerTransition f n) i)
                (Module.DirectLimit.of R ι G f i)
                (positiveTensorPowerSuccEquiv (R := R) (G i) n x))) := by
              rw [directLimitDiagonal_of]
        _ = positiveTensorPowerMap
            (Module.DirectLimit.of R ι G f i) (n + 1) x := by
              rw [positiveTensorPowerSuccEquiv_apply,
                positiveTensorPowerSuccEquiv_symm_apply,
                positiveTensorPowerMap_succ]
              change TensorProduct.map
                  (positiveTensorPowerDirectLimitEquiv f n).toLinearMap
                  (LinearEquiv.refl R
                    (Module.DirectLimit G f)).toLinearMap
                  (TensorProduct.map
                    (Module.DirectLimit.of R ι _
                      (positiveTensorPowerTransition f n) i)
                    (Module.DirectLimit.of R ι G f i) x) = _
              rw [TensorProduct.map_map]
              have hleft :
                  (positiveTensorPowerDirectLimitEquiv f n).toLinearMap.comp
                      (Module.DirectLimit.of R ι _
                        (positiveTensorPowerTransition f n) i) =
                    positiveTensorPowerMap
                      (Module.DirectLimit.of R ι G f i) n := by
                apply LinearMap.ext
                intro y
                exact positiveTensorPowerDirectLimitEquiv_apply_of n i y
              rw [hleft, LinearEquiv.refl_toLinearMap, LinearMap.id_comp]

/-- Eventual-zero detection for every positive tensor power of a directed
module system. -/
theorem exists_eq_zero_of_positiveTensorPowerMap_to_directLimit_eq_zero
    {i : ι} (n : ℕ)
    (x : positiveTensorPower (R := R) (G i) n)
    (hx : positiveTensorPowerMap
      (Module.DirectLimit.of R ι G f i) n x = 0) :
    ∃ j : ι, ∃ hij : i ≤ j,
      positiveTensorPowerTransition f n i j hij x = 0 := by
  have hcolimit :
      Module.DirectLimit.of R ι _
        (positiveTensorPowerTransition f n) i x = 0 := by
    apply (positiveTensorPowerDirectLimitEquiv f n).injective
    rw [positiveTensorPowerDirectLimitEquiv_apply_of, map_zero]
    exact hx
  exact Module.DirectLimit.of.zero_exact hcolimit

end TensorProduct
