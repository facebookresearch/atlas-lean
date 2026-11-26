/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation

/-! Tests for admissible representations: membership in the ring of invariants `S^H` and in the
module `D_S(V) = (S ⊗_F V)^H`, the semilinearity of the diagonal action, the trivial
representation is admissible in the basis form for every action and in the dimension form for
every nontrivial `S`, the transport of both forms along equivariant isomorphisms of algebras, and
matrix representations. -/

open scoped TensorProduct

open Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

-- Scalars from `F` and elements fixed by every `g` are invariant.
example (act : G → S →ₐ[F] S) (H : Subgroup G) (c : F) :
    algebraMap F S c ∈ fixedSubalgebra S act H :=
  Subalgebra.algebraMap_mem _ c

example (act : G → S →ₐ[F] S) (H : Subgroup G) {s : S} (hs : ∀ g, act g s = s) :
    s ∈ fixedSubalgebra S act H :=
  mem_fixedSubalgebra.2 fun g _ => hs g

-- `1 ⊗ v` lies in `D_S(V)` for a vector `v` fixed by `H`, and `D_S(V)` is an `S^H`-module.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) {v : V}
    (hv : ∀ g ∈ H, ρ g v = v) : (1 : S) ⊗ₜ[F] v ∈ ρ.periods act H :=
  mem_periods.2 fun g hg => by
    rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, hv g hg]

example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) {c : S}
    (hc : c ∈ fixedSubalgebra S act H) {x : S ⊗[F] V} (hx : x ∈ ρ.periods act H) :
    c • x ∈ ρ.periods act H :=
  (ρ.periods act H).smul_mem ⟨c, hc⟩ hx

-- The diagonal action `s ⊗ v ↦ act g s ⊗ ρ g v` is semilinear.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (g : G) (a s : S) (v : V) :
    TensorProduct.map (act g).toLinearMap (ρ g) (a • s ⊗ₜ[F] v) =
      (act g a * act g s) ⊗ₜ[F] ρ g v := by
  rw [map_smul_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul,
    AlgHom.toLinearMap_apply]

-- The trivial representation is admissible in the basis form, for every action on `S`: the
-- vectors `1 ⊗ vᵢ` for an `F`-basis `(vᵢ)` of `V` are fixed.
example [FiniteDimensional F V] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    (trivial F G V).HasFixedBasis act H :=
  ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      map_one, trivial_apply]⟩

-- Hence it is admissible in the dimension form when `S` is nontrivial.
example [Nontrivial S] [FiniteDimensional F V] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    (trivial F G V).IsAdmissible act H :=
  HasFixedBasis.isAdmissible ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V),
    fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

-- The trivial representation of `G` on `F`, for the trivial family `act g = id` on `S = F`, is
-- admissible in both forms, and `D_F(F) = F ⊗_F F` has dimension one over `F^H = F`.
example (H : Subgroup G) : (trivial F G F).HasFixedBasis (fun _ => AlgHom.id F F) H :=
  ⟨1, Algebra.TensorProduct.basis F (Module.Basis.singleton (Fin 1) F), fun i g _ => by
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      AlgHom.id_apply, trivial_apply]⟩

example (H : Subgroup G) : (trivial F G F).IsAdmissible (fun _ => AlgHom.id F F) H :=
  HasFixedBasis.isAdmissible
    ⟨1, Algebra.TensorProduct.basis F (Module.Basis.singleton (Fin 1) F), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        AlgHom.id_apply, trivial_apply]⟩

example (H : Subgroup G) :
    Module.finrank (fixedSubalgebra F (fun _ => AlgHom.id F F) H)
      ((trivial F G F).periods (fun _ => AlgHom.id F F) H) = 1 := by
  have h : (trivial F G F).IsAdmissible (fun _ => AlgHom.id F F) H :=
    HasFixedBasis.isAdmissible
      ⟨1, Algebra.TensorProduct.basis F (Module.Basis.singleton (Fin 1) F), fun i g _ => by
        rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
          AlgHom.id_apply, trivial_apply]⟩
  rw [h.2, Module.finrank_self]

-- Transport along the identity, and along conjugation by an automorphism of `S`.
example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) :
    ρ.IsAdmissible act H ↔ ρ.IsAdmissible act H :=
  isAdmissible_iff_of_algEquiv ρ AlgEquiv.refl (fun _ _ => rfl) H

example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) :
    ρ.HasFixedBasis act H ↔ ρ.HasFixedBasis act H :=
  hasFixedBasis_iff_of_algEquiv ρ AlgEquiv.refl (fun _ _ => rfl) H

example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (e : S ≃ₐ[F] S) (H : Subgroup G) :
    ρ.IsAdmissible act H ↔
      ρ.IsAdmissible (fun g => (e : S →ₐ[F] S).comp ((act g).comp e.symm)) H :=
  isAdmissible_iff_of_algEquiv ρ e (fun g s => by simp) H

example (ρ : Representation F G V) (act : G → S →ₐ[F] S) (e : S ≃ₐ[F] S) (H : Subgroup G) :
    ρ.HasFixedBasis act H ↔
      ρ.HasFixedBasis (fun g => (e : S →ₐ[F] S).comp ((act g).comp e.symm)) H :=
  hasFixedBasis_iff_of_algEquiv ρ e (fun g s => by simp) H

-- Matrix representations: `g` acts on `Eⁿ` by the matrix `ρ g`, and the trivial homomorphism
-- gives the trivial representation.
example {E : Type*} [Field E] [Algebra F E] {n : ℕ} (ρ : G →* GL (Fin n) E) (g : G)
    (v : Fin n → E) : ofGL F ρ g v = (ρ g : Matrix (Fin n) (Fin n) E).mulVec v :=
  ofGL_apply ρ g v

example {E : Type*} [Field E] [Algebra F E] {n : ℕ} (g : G) (v : Fin n → E) :
    ofGL F (1 : G →* GL (Fin n) E) g v = v := by
  simp
