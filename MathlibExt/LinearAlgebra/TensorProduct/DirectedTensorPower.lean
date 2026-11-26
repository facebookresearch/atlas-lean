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
# Positive tensor powers of a directed module system

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. The systems P_n(G_i) have colimits canonically equivalent
to P_n(G∞). An element vanishing after this comparison is killed at a common later stage.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Module Module.DirectLimit

namespace TensorProduct

universe u v w x y

variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]

/-- **Positive tensor-power module object.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. The object
positiveTensorPowerModuleObj M n is P_n(M), as a module in the common enlarged universe.
-/
noncomputable def positiveTensorPowerModuleObj
    (M : Type w) [AddCommGroup M] [Module R M] :
    ℕ → ModuleCat.{max u w} R
  | 0 => ModuleCat.of R (R ⊗[R] M)
  | n + 1 => ModuleCat.of R
      ((positiveTensorPowerModuleObj M n : Type (max u w)) ⊗[R] M)

attribute [reducible] positiveTensorPowerModuleObj

/-- **Positive tensor-power carrier.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. The carrier
positiveTensorPower M n is P_n(M).
-/
abbrev positiveTensorPower (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type (max u w) :=
  positiveTensorPowerModuleObj (R := R) M n

/-- **Zero-indexed positive power as a tensor-unit factor.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. The
equivalence positiveTensorPowerZeroEquiv M identifies P_0(M) with R⊗_RM.
-/
noncomputable def positiveTensorPowerZeroEquiv
    (M : Type w) [AddCommGroup M] [Module R M] :
    positiveTensorPower (R := R) M 0 ≃ₗ[R] R ⊗[R] M := by
  with_reducible
    exact LinearEquiv.refl R _

/-- **Successor positive power split into its last factor.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. The
equivalence positiveTensorPowerSuccEquiv M n identifies P_(n+1)(M) with P_n(M)⊗_RM.
-/
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

/-- **Positive tensor-power map of a linear map.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. For R-linear
f:M→N, P_0(f)=id_R⊗f and P_(n+1)(f)=P_n(f)⊗f; this is positiveTensorPowerMap f n.
-/
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

/-- **Positive tensor powers preserve identities.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. For every n,
positiveTensorPowerMap(id_M) n=id_(P_n(M)).
-/
@[simp]
theorem positiveTensorPowerMap_id
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ) :
    positiveTensorPowerMap (LinearMap.id (R := R) (M := M)) n =
      LinearMap.id := by
  induction n with
  | zero => exact LinearMap.lTensor_id (R := R) R M
  | succ n ih =>
      rw [positiveTensorPowerMap_succ, ih, TensorProduct.map_id]

/-- **Positive tensor powers preserve composition.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. For linear
f:M→N,g:N→Q, P_n(g∘f)=P_n(g)∘P_n(f).
-/
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

/-- **Positive tensor-power equivalence induced by a module equivalence.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. For a linear
equivalence e:M≃N, positiveTensorPowerCongr e n:P_n(M)≃ₗ[R]P_n(N) has map P_n(e) and inverse
P_n(e⁻¹).
-/
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

/-- **Naturality of the zero positive-power identification.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. For linear
f:M→N, the maps P_0(f) and id_R⊗f agree through the zero-index identifications P_0(X)≃R⊗X.
-/
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

/-- **Naturality of the last-factor positive-power split.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. For linear
f:M→N, splitting P_(n+1)(f) gives P_n(f)⊗f under P_(n+1)(X)≃P_n(X)⊗X.
-/
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

/-- **Stage transition in a positive tensor-power system.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. The transition positiveTensorPowerTransition n i j is
P_n(f_ij).
-/
noncomputable def positiveTensorPowerTransition
    (n : ℕ) (i j : ι) (hij : i ≤ j) :
    positiveTensorPower (R := R) (G i) n →ₗ[R]
      positiveTensorPower (R := R) (G j) n :=
  positiveTensorPowerMap (f i j hij) n

attribute [reducible] positiveTensorPowerTransition

omit [DecidableEq ι] [IsDirectedOrder ι]
  [DirectedSystem G (f · · ·)] in
/-- **Successor split respects a tensor-power stage transition.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. Under the last-factor splits, P_(n+1)(f_ij) equals
P_n(f_ij)⊗f_ij.
-/
theorem positiveTensorPowerSuccEquiv_transition_naturality
    (n : ℕ) (i j : ι) (hij : i ≤ j) :
    (positiveTensorPowerSuccEquiv (R := R) (G j) n).toLinearMap.comp
        (positiveTensorPowerTransition f (n + 1) i j hij) =
      (diagonalTransition
        (positiveTensorPowerTransition f n) f i j hij).comp
        (positiveTensorPowerSuccEquiv (R := R) (G i) n).toLinearMap := by
  simpa only [positiveTensorPowerTransition, diagonalTransition] using
    positiveTensorPowerSuccEquiv_naturality (f i j hij) n

/-- **Positive tensor powers form a directed system.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. For fixed n, the modules P_n(G_i) and transitions
P_n(f_ij) satisfy the directed-system identities and composition laws.
-/
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

/-- **Direct limit of a positive tensor-power system.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. The equivalence positiveTensorPowerDirectLimitEquiv
n:colim_iP_n(G_i)≃ₗ[R]P_n(G∞) is induced by P_n(j_i).
-/
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

/-- **Tensor-power limit equivalence on a stage representative.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. For x∈P_n(G_i), the canonical limit class maps to
P_n(j_i)(x).
-/
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

/-- **Eventual zero in a positive tensor-power system.**

For an R-module M over a commutative ring, define P_0(M)=R⊗_RM and P_(n+1)(M)=P_n(M)⊗_RM,
left-associated. Thus index n has n+1 factors of M and a leading tensor unit R. Let R be a
commutative ring, I an upward-directed preorder and (G_i,f_ij) a directed system of R-modules,
with stage maps j_i:G_i→G∞=colim G. If x∈P_n(G_i) satisfies P_n(j_i)(x)=0, then some j≥i has
P_n(f_ij)(x)=0.
-/
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
