/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Identity

/-!
# Composition of induction functors

The composite induction adjunction and uniqueness of left adjoints give an isomorphism between
iterated and composite induction. Its pure-tensor formula is `s ⊗ (r ⊗ m) ↦ (s * ψ r) ⊗ m`. ULift
comparisons extend the formulas to independent scalar and coefficient worlds.
-/

@[expose] public section

open CategoryTheory

universe u v s w

namespace ModuleCat.RingHomInduction

section NativeHom

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- The adjunction evaluates on the unit tensor. -/
theorem nativeHomEquiv_apply (M : ModuleCat.{max u v w} k) (N : ModuleCat.{max u v w} R)
    (f : (ModuleCat.induceScalars.{u, v, w} φ).obj M ⟶ N) (m : M) :
    (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).homEquiv M N f m =
      f (tensor φ M 1 m) := by
  rw [Adjunction.homEquiv_unit]
  change f ((ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).unit.app M m) = _
  rw [ModuleCat.induceRestrictScalarsAdj_unit]

end NativeHom

section Congruence

variable {k : Type u} {R : Type v} [Ring k] [Ring R]
  {φ φ' : k →+* R}

/-- Transport the right adjoint along an equality of the ring homomorphisms. -/
noncomputable def congruenceAdj (h : φ = φ') : ModuleCat.induceScalars.{u, v, w} φ ⊣
    ModuleCat.restrictScalars.{max u v w} φ' :=
  (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).ofNatIsoRight
    (ModuleCat.restrictScalarsCongr h)

theorem congruenceAdj_hom_apply (h : φ = φ')
    (M : ModuleCat.{max u v w} k) (N : ModuleCat.{max u v w} R)
    (f : (ModuleCat.induceScalars.{u, v, w} φ).obj M ⟶ N) (m : M) :
    (congruenceAdj h).homEquiv M N f m = f (tensor φ M 1 m) := by
  rw [congruenceAdj, Adjunction.homEquiv_ofNatIsoRight_apply]
  change (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ).homEquiv M N f m = _
  exact nativeHomEquiv_apply φ M N f m

/-- Uniqueness gives the induction transport for equal scalar homomorphisms. -/
noncomputable def congrIso (h : φ = φ') : ModuleCat.induceScalars.{u, v, w} φ ≅
    ModuleCat.induceScalars.{u, v, w} φ' :=
  Adjunction.leftAdjointUniq (congruenceAdj h)
    (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ')

theorem congrIso_hom_unit (h : φ = φ') (M : ModuleCat.{max u v w} k) (m : M) :
    (congrIso h).hom.app M (tensor φ M 1 m) = tensor φ' M 1 m := by
  let N : ModuleCat.{max u v w} R := (ModuleCat.induceScalars.{u, v, w} φ').obj M
  let G := ModuleCat.restrictScalars.{max u v w} φ'
  let μ : (ModuleCat.induceScalars.{u, v, w} φ).obj M ⟶ N := (congrIso h).hom.app M
  have he : (congruenceAdj h).homEquiv M N μ =
      (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ').unit.app M :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (congruenceAdj h)
      (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ') M
  have hm := congrArg (fun q : M ⟶ G.obj N => (show N from q m)) he
  have hl : (show N from (congruenceAdj h).homEquiv M N μ m) = μ (tensor φ M 1 m) := by
    exact congruenceAdj_hom_apply h M N μ m
  have hr : (show N from (ModuleCat.induceRestrictScalarsAdj.{u, v, w} φ').unit.app M m) =
      tensor φ' M 1 m := by
    exact ModuleCat.induceRestrictScalarsAdj_unit φ' M m
  exact hl.symm.trans (hm.trans hr)

theorem congrIso_hom_tensor (h : φ = φ') (M : ModuleCat.{max u v w} k)
    (r : R) (m : M) :
    (congrIso h).hom.app M (tensor φ M r m) = tensor φ' M r m := by
  let N : ModuleCat.{max u v w} R := (ModuleCat.induceScalars.{u, v, w} φ').obj M
  let μ : (ModuleCat.induceScalars.{u, v, w} φ).obj M ⟶ N := (congrIso h).hom.app M
  let x : N := tensor φ' M 1 m
  have hr : tensor φ M r m = r • tensor φ M 1 m := by
    simpa only [mul_one] using (smul_tensor φ M r 1 m).symm
  have hu : μ (tensor φ M 1 m) = x := congrIso_hom_unit h M m
  have h₁ : μ (tensor φ M r m) = r • μ (tensor φ M 1 m) :=
    (congrArg μ hr).trans (μ.hom.map_smul r (tensor φ M 1 m))
  have h₂ : r • μ (tensor φ M 1 m) = r • x := congrArg (fun y : N => r • y) hu
  have h₃ : r • x = (show N from tensor φ' M r m) := by
    change r • tensor φ' M 1 m = tensor φ' M r m
    rw [smul_tensor, mul_one]
  exact h₁.trans (h₂.trans h₃)

end Congruence

section Composition

variable {k : Type u} {R : Type v} {S : Type s} [Ring k] [Ring R] [Ring S]
  (φ : k →+* R) (ψ : R →+* S)


/-- Compose the adjunctions and transport their right adjoint by scalar restriction. -/
noncomputable def compositionAdj : (ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙ (ModuleCat.induceScalars.{v, s,
  max u v s w} ψ) ⊣ (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ)) :=
  ((ModuleCat.induceRestrictScalarsAdj.{u, v, max u v s w} φ).comp (ModuleCat.induceRestrictScalarsAdj.{v, s, max u v
    s w} ψ)).ofNatIsoRight (ModuleCat.restrictScalarsComp.{max u v s w} φ ψ).symm

/-- The composed Hom equivalence evaluates at both unit tensors. -/
theorem composedHomEquiv_apply (M : ModuleCat.{max u v s w} k)
    (N : ModuleCat.{max u v s w} S) (f : ((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M ⟶ N) (m : M) :
    ((ModuleCat.induceRestrictScalarsAdj.{u, v, max u v s w} φ).comp (ModuleCat.induceRestrictScalarsAdj.{v, s, max u
      v s w} ψ)).homEquiv M N f m =
      f (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := by
  rw [Adjunction.comp_homEquiv]
  let K : ModuleCat.{max u v s w} R := (ModuleCat.induceScalars.{u, v, max u v s w} φ).obj M
  let y : K := tensor φ M 1 m
  let N' : ModuleCat.{max u v s w} R := (ModuleCat.restrictScalars.{max u v s w} ψ).obj N
  let q : K ⟶ N' := (ModuleCat.induceRestrictScalarsAdj.{v, s, max u v s w} ψ).homEquiv K N f
  have h₁ : (show N from (ModuleCat.induceRestrictScalarsAdj.{u, v, max u v s w} φ).homEquiv M N' q m) = (show N from
    q y) := by
    exact nativeHomEquiv_apply.{u, v, max u v s w} φ M N' q m
  have h₂ : (show N from q y) = f (tensor ψ K 1 y) := by
    exact nativeHomEquiv_apply.{v, s, max u v s w} ψ K N f y
  exact h₁.trans h₂

/-- Restriction-composition transport is the identity on elements. -/
theorem compositionAdj_hom_apply (M : ModuleCat.{max u v s w} k)
    (N : ModuleCat.{max u v s w} S) (f : ((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M ⟶ N) (m : M) :
    (compositionAdj.{u, v, s, w} φ ψ).homEquiv M N f m =
      f (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := by
  rw [compositionAdj, Adjunction.homEquiv_ofNatIsoRight_apply]
  change ((ModuleCat.induceRestrictScalarsAdj.{u, v, max u v s w} φ).comp (ModuleCat.induceRestrictScalarsAdj.{v, s,
    max u v s w} ψ)).homEquiv M N f m = _
  exact composedHomEquiv_apply.{u, v, s, w} φ ψ M N f m

/-- The induction comparison comes from uniqueness of left adjoints. -/
noncomputable def compositionIso : (ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙ (ModuleCat.induceScalars.{v, s,
  max u v s w} ψ) ≅ (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ))  :=
  let e₁ : (ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙ (ModuleCat.induceScalars.{v, s, max u v s w} ψ) ⊣
    (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ)) := compositionAdj.{u, v, s, w} φ ψ
  let e₂ : (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)) ⊣ (ModuleCat.restrictScalars.{max u v s w} (ψ.comp
    φ)) := (ModuleCat.induceRestrictScalarsAdj.{u, s, max u v s w} (ψ.comp φ))
  Adjunction.leftAdjointUniq (C := ModuleCat.{max u v s w} k)
    (D := ModuleCat.{max u v s w} S) (F := (ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s,
    max u v s w} ψ)) (F' := (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ))) (G :=
    (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ))) e₁ e₂

/-- The comparison carries the composed unit to the direct unit. -/
theorem compositionIso_hom_unit (M : ModuleCat.{max u v s w} k) (m : M) :
    (compositionIso.{u, v, s, w} φ ψ).hom.app M
        (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) = tensor (ψ.comp φ) M 1 m := by
  let N : ModuleCat.{max u v s w} S := (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)).obj M
  let G := (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ))
  let μ : ((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙ (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M ⟶
    N := (compositionIso.{u, v, s, w} φ ψ).hom.app M
  have he : (compositionAdj.{u, v, s, w} φ ψ).homEquiv M N μ = (ModuleCat.induceRestrictScalarsAdj.{u, s, max u v s w}
    (ψ.comp
    φ)).unit.app M :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (compositionAdj.{u, v, s, w} φ ψ)
      (ModuleCat.induceRestrictScalarsAdj.{u, s, max u
      v s w} (ψ.comp φ)) M
  have hm := congrArg (fun q : M ⟶ G.obj N => (show N from q m)) he
  have hl : (show N from (compositionAdj.{u, v, s, w} φ ψ).homEquiv M N μ m) =
      μ (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := by
    exact compositionAdj_hom_apply.{u, v, s, w} φ ψ M N μ m
  have hr : (show N from (ModuleCat.induceRestrictScalarsAdj.{u, s, max u v s w} (ψ.comp φ)).unit.app M m) = tensor
    (ψ.comp φ) M 1 m := by
    exact ModuleCat.induceRestrictScalarsAdj_unit.{u, s, max u v s w} (ψ.comp φ) M m
  exact hl.symm.trans (hm.trans hr)

/-- The multiplication order is computed from the balancing relation. -/
theorem compositionIso_hom_tensor (M : ModuleCat.{max u v s w} k)
    (b : S) (r : R) (m : M) :
    (compositionIso.{u, v, s, w} φ ψ).hom.app M
        (tensor ψ (Carrier φ M) b (tensor φ M r m)) =
      tensor (ψ.comp φ) M (b * ψ r) m := by
  let N : ModuleCat.{max u v s w} S := (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)).obj M
  let μ : ((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙ (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M ⟶
    N := (compositionIso.{u, v, s, w} φ ψ).hom.app M
  have hi : tensor φ M r m = r • tensor φ M 1 m := by
    simpa only [mul_one] using (smul_tensor φ M r 1 m).symm
  have hb : tensor ψ (Carrier φ M) b (tensor φ M r m) =
      (b * ψ r) • tensor ψ (Carrier φ M) 1 (tensor φ M 1 m) := by
    rw [hi, ← tensor_balance ψ (Carrier φ M) r b (tensor φ M 1 m)]
    simpa only [mul_one] using
      (smul_tensor ψ (Carrier φ M) (b * ψ r) 1 (tensor φ M 1 m)).symm
  let x : N := tensor (ψ.comp φ) M 1 m
  have hu : μ (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) = x :=
    compositionIso_hom_unit.{u, v, s, w} φ ψ M m
  have h₁ : μ (tensor ψ (Carrier φ M) b (tensor φ M r m)) =
      μ ((b * ψ r) • tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := congrArg μ hb
  have h₂ : μ ((b * ψ r) • tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) =
      (b * ψ r) • μ (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := μ.hom.map_smul _ _
  have h₃ : (b * ψ r) • μ (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) =
      (b * ψ r) • x := congrArg (fun y : N => (b * ψ r) • y) hu
  have h₄ : (b * ψ r) • x = (show N from tensor (ψ.comp φ) M (b * ψ r) m) := by
    change (b * ψ r) • tensor (ψ.comp φ) M 1 m = tensor (ψ.comp φ) M (b * ψ r) m
    rw [smul_tensor, mul_one]
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem compositionIso_inv_tensor (M : ModuleCat.{max u v s w} k) (b : S) (m : M) :
    (compositionIso.{u, v, s, w} φ ψ).inv.app M (tensor (ψ.comp φ) M b m) =
      tensor ψ (Carrier φ M) b (tensor φ M 1 m) := by
  let e := ((compositionIso.{u, v, s, w} φ ψ).app M).toLinearEquiv
  change e.symm (tensor (ψ.comp φ) M b m) = _
  have h : e (tensor ψ (Carrier φ M) b (tensor φ M 1 m)) =
      tensor (ψ.comp φ) M b m := by
    change (compositionIso.{u, v, s, w} φ ψ).hom.app M
      (tensor ψ (Carrier φ M) b (tensor φ M 1 m)) = tensor (ψ.comp φ) M b m
    simpa only [ψ.map_one, mul_one] using compositionIso_hom_tensor.{u, v, s, w} φ ψ M b 1 m
  exact (congrArg e.symm h).symm.trans (e.symm_apply_apply _)

/-- Hom-equivalence injectivity reduces equality to unit representatives. -/
theorem composition_hom_ext (M : ModuleCat.{max u v s w} k)
    (N : ModuleCat.{max u v s w} S) {f g : ((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M ⟶ N}
    (h : ∀ m : M, f (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) =
      g (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m))) : f = g := by
  apply ((compositionAdj.{u, v, s, w} φ ψ).homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hf : (show N from (compositionAdj.{u, v, s, w} φ ψ).homEquiv M N f m) =
      f (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := by
    exact compositionAdj_hom_apply.{u, v, s, w} φ ψ M N f m
  have hg : (show N from (compositionAdj.{u, v, s, w} φ ψ).homEquiv M N g m) =
      g (tensor ψ (Carrier φ M) 1 (tensor φ M 1 m)) := by
    exact compositionAdj_hom_apply.{u, v, s, w} φ ψ M N g m
  exact hf.trans ((h m).trans hg.symm)

variable (M : Type w) [AddCommGroup M] [Module k M]

/-- The comparison for every carrier is transported through ULifts. -/
noncomputable def compositionEquiv :
    Carrier ψ (Carrier φ M) ≃ₗ[S] Carrier (ψ.comp φ) M :=
  let eInput : Carrier φ (ULift.{max u v s} M) ≃ₗ[R] Carrier φ M := liftedInputEquiv φ M
  let eNative : Carrier ψ (Carrier φ (ULift.{max u v s} M)) ≃ₗ[S]
      Carrier (ψ.comp φ) (ULift.{max u v s} M) :=
    ((compositionIso.{u, v, s, w} φ ψ).app (ModuleCat.of k (ULift.{max u v s} M))).toLinearEquiv
  let eOutput : Carrier (ψ.comp φ) (ULift.{max u v s} M) ≃ₗ[S]
      Carrier (ψ.comp φ) M := liftedInputEquiv (ψ.comp φ) M
  (mapEquiv ψ eInput.symm).trans (eNative.trans eOutput)

theorem compositionEquiv_tensor (b : S) (r : R) (m : M) :
    compositionEquiv φ ψ M (tensor ψ (Carrier φ M) b (tensor φ M r m)) =
      tensor (ψ.comp φ) M (b * ψ r) m := by
  let L := ModuleCat.of k (ULift.{max u v s} M)
  change liftedInputEquiv (ψ.comp φ) M
    ((compositionIso.{u, v, s, w} φ ψ).hom.app L
      (mapEquiv ψ
        (liftedInputEquiv φ M : Carrier φ (ULift.{max u v s} M) ≃ₗ[R] Carrier φ M).symm
        (tensor ψ (Carrier φ M) b (tensor φ M r m)))) = _
  rw [mapEquiv_tensor, liftedInputEquiv_symm_tensor,
    compositionIso_hom_tensor, liftedInputEquiv_tensor]

theorem compositionEquiv_symm_tensor (b : S) (m : M) :
    (compositionEquiv φ ψ M).symm (tensor (ψ.comp φ) M b m) =
      tensor ψ (Carrier φ M) b (tensor φ M 1 m) := by
  apply (compositionEquiv φ ψ M).injective
  rw [LinearEquiv.apply_symm_apply, compositionEquiv_tensor, ψ.map_one, mul_one]

end Composition

end ModuleCat.RingHomInduction
