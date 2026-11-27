/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Dual

/-! Tests for duals of admissible representations: the pairing between `S ⊗_F V*` and `S ⊗_F V`
on pure tensors, its perfectness for finite-dimensional `V` and its equivariance, Fontaine's
natural map `D_S(V*) → D_S(V)*`, the basis of `S ⊗_F V*` dual to a basis of `S ⊗_F V`, and the
trivial representation, whose dual is admissible in the basis form with `D_S(V*) ≃ D_S(V)*`;
and, for a regular ring, the dual of an admissible representation. -/

open scoped TensorProduct

open Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

-- The pairing on pure tensors: `⟨a ⊗ φ, b ⊗ v⟩ = a b φ(v)`, so `⟨1 ⊗ φ, 1 ⊗ v⟩ = φ(v)`.
example (a b : S) (φ : Module.Dual F V) (v : V) :
    baseChangeDualPairing F S V (a ⊗ₜ φ) (b ⊗ₜ v) = a * b * algebraMap F S (φ v) := by
  simp

example (φ : Module.Dual F V) (v : V) :
    baseChangeDualPairing F S V (1 ⊗ₜ φ) (1 ⊗ₜ v) = algebraMap F S (φ v) := by
  simp

-- For finite-dimensional `V`, the pairing identifies `S ⊗_F V*` with `(S ⊗_F V)*`: it is
-- nondegenerate on the left, and every `S`-linear form on `S ⊗_F V` is a pairing.
example [FiniteDimensional F V] : Function.Bijective (baseChangeDualPairing F S V) :=
  baseChangeDualPairing_bijective

example [FiniteDimensional F V] {x : S ⊗[F] Module.Dual F V}
    (hx : ∀ y, baseChangeDualPairing F S V x y = 0) : x = 0 :=
  baseChangeDualPairing_bijective.1 (by
    rw [map_zero]
    exact LinearMap.ext hx)

example [FiniteDimensional F V] (f : Module.Dual S (S ⊗[F] V)) :
    ∃ x, baseChangeDualPairing F S V x = f :=
  baseChangeDualPairing_bijective.2 f

-- The pairing is equivariant for the diagonal actions, and invariant when `G` acts trivially on
-- `S`.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (g : G) (x : S ⊗[F] Module.Dual F V)
    (y : S ⊗[F] V) :
    baseChangeDualPairing F S V (TensorProduct.map (act g).toLinearMap (ρ.dual g) x)
        (TensorProduct.map (act g).toLinearMap (ρ g) y) =
      act g (baseChangeDualPairing F S V x y) :=
  baseChangeDualPairing_map_map ρ act g x y

example (ρ : Representation F G V) (g : G) (x : S ⊗[F] Module.Dual F V) (y : S ⊗[F] V) :
    baseChangeDualPairing F S V ((ρ.dual g).lTensor S x) ((ρ g).lTensor S y) =
      baseChangeDualPairing F S V x y :=
  baseChangeDualPairing_map_map ρ (fun _ => AlgHom.id F S) g x y

-- Fontaine's natural map `D_S(V*) → D_S(V)*` is given by the pairing, which takes values in `S^H`
-- on `D_S(V*) × D_S(V)`.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    (x : ρ.dual.periods act H) (y : ρ.periods act H) :
    (ρ.periodsDual act H x y : S) = baseChangeDualPairing F S V x y := by
  simp

example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    {x : S ⊗[F] Module.Dual F V} (hx : x ∈ ρ.dual.periods act H) {y : S ⊗[F] V}
    (hy : y ∈ ρ.periods act H) :
    baseChangeDualPairing F S V x y ∈ fixedSubalgebra S act H :=
  baseChangeDualPairing_mem_fixedSubalgebra hx hy

-- For the trivial representation, `1 ⊗ φ ∈ D_S(V*)` and `1 ⊗ v ∈ D_S(V)` pair to `φ(v)`.
example (act : G → S →ₐ[F] S) (H : Subgroup G) (φ : Module.Dual F V) (v : V) :
    ((trivial F G V).periodsDual act H
        ⟨1 ⊗ₜ φ, mem_periods.2 fun g _ => by
          rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
          congr 1⟩
        ⟨1 ⊗ₜ v, mem_periods.2 fun g _ => by
          rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, trivial_apply]⟩ : S) =
      algebraMap F S (φ v) := by
  simp

-- The basis of `S ⊗_F V*` dual to a basis `(bᵢ)` of `S ⊗_F V` satisfies `⟨b'ᵢ, bⱼ⟩ = δᵢⱼ`; the
-- basis dual to `(1 ⊗ vᵢ)` for an `F`-basis `(vᵢ)` of `V` is `(1 ⊗ vᵢ*)`.
example [FiniteDimensional F V] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι S (S ⊗[F] V)) (i j : ι) :
    baseChangeDualPairing F S V (baseChangeDualBasis b i) (b j) = if j = i then 1 else 0 := by
  rw [baseChangeDualPairing_baseChangeDualBasis, Module.Basis.dualBasis_apply_self]

example [FiniteDimensional F V] (i : Fin (Module.finrank F V)) :
    baseChangeDualBasis (Algebra.TensorProduct.basis S (Module.finBasis F V)) i =
      (1 : S) ⊗ₜ (Module.finBasis F V).dualBasis i := by
  refine baseChangeDualPairing_bijective.1
    ((Algebra.TensorProduct.basis S (Module.finBasis F V)).ext fun j => ?_)
  rw [baseChangeDualPairing_baseChangeDualBasis, Module.Basis.dualBasis_apply_self,
    Algebra.TensorProduct.basis_apply, baseChangeDualPairing_tmul_tmul,
    Module.Basis.dualBasis_apply_self]
  split_ifs <;> simp

-- The trivial representation: its dual is admissible in the basis form, hence in the dimension
-- form when `S` is nontrivial, and `D_S(V*) ≃ D_S(V)*`.
example [FiniteDimensional F V] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    (trivial F G V).dual.HasFixedBasis act H :=
  HasFixedBasis.dual ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      map_one, trivial_apply]⟩

example [Nontrivial S] [FiniteDimensional F V] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    (trivial F G V).dual.IsAdmissible act H :=
  HasFixedBasis.isAdmissible <| HasFixedBasis.dual
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

example [FiniteDimensional F V] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    Function.Bijective ((trivial F G V).periodsDual act H) :=
  HasFixedBasis.periodsDual_bijective
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

example [FiniteDimensional F V] (act : G → S →ₐ[F] S) (H : Subgroup G)
    (h : (trivial F G V).HasFixedBasis act H) (x : (trivial F G V).dual.periods act H)
    (y : (trivial F G V).periods act H) :
    (h.periodsDualEquiv x y : S) = baseChangeDualPairing F S V x y := by
  simp

-- For the trivial family `act g = id` on `S = F`, `D_F(F*) ≃ D_F(F)*` over `F^H`.
noncomputable example (H : Subgroup G) :
    (trivial F G F).dual.periods (fun _ => AlgHom.id F F) H ≃ₗ[fixedSubalgebra F
      (fun _ => AlgHom.id F F) H]
      Module.Dual (fixedSubalgebra F (fun _ => AlgHom.id F F) H)
        ((trivial F G F).periods (fun _ => AlgHom.id F F) H) :=
  HasFixedBasis.periodsDualEquiv
    ⟨1, Algebra.TensorProduct.basis F (Module.Basis.singleton (Fin 1) F), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        AlgHom.id_apply, trivial_apply]⟩

-- For a regular ring, the dual of an admissible representation is admissible, and
-- `D_S(V*) → D_S(V)*` is an isomorphism; for instance for a field with any action.
example [IsDomain S] {act : G →* (S →ₐ[F] S)} {H : Subgroup G}
    (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} (h : ρ.IsAdmissible act H) :
    ρ.dual.IsAdmissible act H ∧ Function.Bijective (ρ.periodsDual act H) :=
  ⟨hS.isAdmissible_dual h, hS.periodsDual_bijective h⟩

example {L : Type*} [Field L] [Algebra F L] (act : G →* (L →ₐ[F] L)) (H : Subgroup G)
    {ρ : Representation F G V} (h : ρ.IsAdmissible act H) :
    ρ.dual.dual.IsAdmissible act H :=
  have hL := isRegularPeriodRing_of_isField (Field.toIsField L) act H
  hL.isAdmissible_dual (hL.isAdmissible_dual h)
