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
# Positive tensor powers and directed limits

Let R be a commutative ring. For an R-module M, the positive tensor power
indexed by n has n + 1 copies of M with a leading tensor unit:
T₀(M) = R ⊗[R] M and T_(n+1)(M) = T_n(M) ⊗[R] M.
Its carrier lies in max(u, w), where u is the ring universe and w the
module universe. A linear map acts on every copy of M and as id_R
on the leading unit, respecting identity and composition.

For a directed system G_i of R-modules with additive commutative group
structures over a directed preorder with decidable equality, these powers
form directed systems. Their direct limits satisfy
lim_i T_n(G_i) ≅ T_n(lim_i G_i).
The forward comparison is T_n(of_i) on each stage. An element becoming
zero under this stage map vanishes after a single later transition.
Ring, index and module carrier universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Module Module.DirectLimit

namespace TensorProduct

universe u v w x y

variable {R : Type u} {ι : Type v} [CommRing R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]

/-- Let R be a commutative ring and M an R-module with additive
commutative group structure. Define T₀(M) = R ⊗[R] M and
T_(n+1)(M) = T_n(M) ⊗[R] M.
This is the corresponding R-module object in ModuleCat max(u, w),
where R has universe u and M has universe w.
It has n + 1 copies of M in left-associated order with leading unit R. -/
noncomputable def positiveTensorPowerModuleObj
    (M : Type w) [AddCommGroup M] [Module R M] :
    ℕ → ModuleCat.{max u w} R
  | 0 => ModuleCat.of R (R ⊗[R] M)
  | n + 1 => ModuleCat.of R
      ((positiveTensorPowerModuleObj M n : Type (max u w)) ⊗[R] M)

attribute [reducible] positiveTensorPowerModuleObj

/-- Let R be a commutative ring and M an R-module with additive
commutative group structure. Define T₀(M) = R ⊗[R] M and
T_(n+1)(M) = T_n(M) ⊗[R] M.
The carrier of T_n(M) is positiveTensorPower M n, in universe max(u, w).
It retains the R-module structure of the iterated tensor product. -/
abbrev positiveTensorPower (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℕ) : Type (max u w) :=
  positiveTensorPowerModuleObj (R := R) M n

/-- Let R be a commutative ring and M an R-module with additive
commutative group structure. Define T₀(M) = R ⊗[R] M and
T_(n+1)(M) = T_n(M) ⊗[R] M.
The index-zero splitting identifies T₀(M) with R ⊗[R] M
as an R-module. The initial tensor unit remains explicit. -/
noncomputable def positiveTensorPowerZeroEquiv
    (M : Type w) [AddCommGroup M] [Module R M] :
    positiveTensorPower (R := R) M 0 ≃ₗ[R] R ⊗[R] M := by
  with_reducible
    exact LinearEquiv.refl R _

/-- Let R be a commutative ring and M an R-module with additive
commutative group structure. Define T₀(M) = R ⊗[R] M and
T_(n+1)(M) = T_n(M) ⊗[R] M.
For every n ∈ ℕ, this is the R-linear final-factor splitting
T_(n+1)(M) ≅ T_n(M) ⊗[R] M, retaining the left-associated factor order. -/
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

/-- For a commutative ring R and an R-linear map f : M → N between
R-modules with additive commutative group structures, this is
T_n(f) : T_n(M) → T_n(N).
It is id_R ⊗ f when n = 0 and T_n(f) ⊗ f at the next index.
The source and target module universes may be independent. -/
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

/-- Let R be a commutative ring and M an R-module with additive
commutative group structure. Define T₀(M) = R ⊗[R] M and
T_(n+1)(M) = T_n(M) ⊗[R] M.
For every n ∈ ℕ, T_n(id_M) = id_(T_n(M)). -/
@[simp]
theorem positiveTensorPowerMap_id
    (M : Type w) [AddCommGroup M] [Module R M] (n : ℕ) :
    positiveTensorPowerMap (LinearMap.id (R := R) (M := M)) n =
      LinearMap.id := by
  induction n with
  | zero => exact LinearMap.lTensor_id (R := R) R M
  | succ n ih =>
      rw [positiveTensorPowerMap_succ, ih, TensorProduct.map_id]

/-- For a commutative ring R, R-linear f : M → N and g : N → P,
and n ∈ ℕ, the induced tensor-power maps satisfy
T_n(g ∘ f) = T_n(g) ∘ T_n(f).
All three module carrier universes may be independent. -/
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

/-- For a commutative ring R, an R-linear equivalence e : M ≅ N
between R-modules with additive commutative group structures induces
T_n(M) ≅ₗ[R] T_n(N) for every n ∈ ℕ.
Its forward map is T_n(e) and its inverse is T_n(e⁻¹). -/
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

/-- For a commutative ring R and an R-linear map g : M → N,
the initial splittings ζ_M : T₀(M) ≅ R ⊗[R] M and
ζ_N : T₀(N) ≅ R ⊗[R] N satisfy
ζ_N ∘ T₀(g) = (id_R ⊗ g) ∘ ζ_M. -/
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

/-- For a commutative ring R and an R-linear map g : M → N,
the final-factor splittings ξ_M : T_(n+1)(M) ≅ T_n(M) ⊗[R] M
and ξ_N for N satisfy
ξ_N ∘ T_(n+1)(g) = (T_n(g) ⊗ g) ∘ ξ_M. -/
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

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
For n ∈ ℕ and i ≤ j, the positive-power transition
T_n(G_i) → T_n(G_j) is T_n(f_ij), applying the given transition
to each module factor and id_R to the leading unit. -/
noncomputable def positiveTensorPowerTransition
    (n : ℕ) (i j : ι) (hij : i ≤ j) :
    positiveTensorPower (R := R) (G i) n →ₗ[R]
      positiveTensorPower (R := R) (G j) n :=
  positiveTensorPowerMap (f i j hij) n

attribute [reducible] positiveTensorPowerTransition

omit [DecidableEq ι] [IsDirectedOrder ι]
  [DirectedSystem G (f · · ·)] in
/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
For i ≤ j, splitting off the last factor commutes with the
positive-power transition:
ξ_j ∘ T_(n+1)(f_ij) = (T_n(f_ij) ⊗ f_ij) ∘ ξ_i.
The target transition is the simultaneous tensor transition on
the systems T_n(G_i) and G_i. -/
theorem positiveTensorPowerSuccEquiv_transition_naturality
    (n : ℕ) (i j : ι) (hij : i ≤ j) :
    (positiveTensorPowerSuccEquiv (R := R) (G j) n).toLinearMap.comp
        (positiveTensorPowerTransition f (n + 1) i j hij) =
      (diagonalTransition
        (positiveTensorPowerTransition f n) f i j hij).comp
        (positiveTensorPowerSuccEquiv (R := R) (G i) n).toLinearMap := by
  simpa only [positiveTensorPowerTransition, diagonalTransition] using
    positiveTensorPowerSuccEquiv_naturality (f i j hij) n

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
For every n ∈ ℕ, the modules T_n(G_i) and transitions T_n(f_ij)
satisfy the directed-system identity and composition laws. -/
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

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
For every n ∈ ℕ, this is the R-linear direct-limit equivalence
lim_i T_n(G_i) ≅ T_n(lim_i G_i).
On a stage class represented by x ∈ T_n(G_i), its forward map is
T_n(of_i)(x), with of_i : G_i → lim G the canonical inclusion. -/
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

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
The direct-limit comparison in positive index n has the stage value
comparison(of_i(x)) = T_n(of_i)(x) for every x ∈ T_n(G_i).
The stage map on the left is into lim_i T_n(G_i). -/
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

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
If x ∈ T_n(G_i) maps to zero under T_n(of_i) in T_n(lim G),
there is j ≥ i such that the transition T_n(f_ij) sends x to zero.
This holds for every n ∈ ℕ, using T₀(G_i) = R ⊗[R] G_i. -/
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
