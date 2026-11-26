/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen.lean`,
`P2M/Sol/S_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen.lean`,
`Theorems/Thm_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit.lean`,
`P2M/Sol/S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit.lean`,
`Theorems/Thm_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow.lean`
and
`P2M/Sol/S_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import MathlibExt.RingTheory.Etale.AdjoinRootPowSub

@[expose] public section



set_option autoImplicit false

universe u

open Polynomial TensorProduct

namespace KummerIntegralClosureKa

variable {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]

private theorem mem_range_includeLeft_of_isIntegral {S : Type*} [CommRing S] [Algebra A S]
  [Algebra.Smooth A S]
    (y : S ⊗[A] K) (hy : IsIntegral S y) :
    y ∈ (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] K).range := by
  obtain ⟨z, hz⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := A) (S := S) (B := K)).2 ⟨y, hy⟩
  have hz' : ((TensorProduct.toIntegralClosure A S K z : integralClosure S (S ⊗[A] K)) : S ⊗[A] K)
    = y := by
    rw [hz]
  rw [← hz']
  clear hz hz' hy y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      obtain ⟨a, ha⟩ := a
      have ha' : a ∈ integralClosure A K := ha
      rw [IsIntegrallyClosed.integralClosure_eq_bot A K, Algebra.mem_bot] at ha'
      obtain ⟨a₀, rfl⟩ := ha'
      refine ⟨a₀ • s, ?_⟩
      simp only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
        Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, Subalgebra.coe_val]
      rw [Algebra.TensorProduct.includeLeftRingHom_apply, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      rw [map_add, Subalgebra.coe_add]
      exact add_mem hx hy

variable (K)

private noncomputable abbrev fA (n : ℕ) (u : A) : A[X] := X ^ n - C u

private noncomputable abbrev fK (n : ℕ) (u : A) : K[X] := X ^ n - C (algebraMap A K u)

variable {K}

private theorem root_fK_pow (n : ℕ) (u : A) :
    (AdjoinRoot.root (fK K n u)) ^ n = algebraMap A (AdjoinRoot (fK K n u)) u := by
  have h := AdjoinRoot.eval₂_root (fK K n u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h, IsScalarTower.algebraMap_apply A K (AdjoinRoot (fK K n u))]
  rfl

-- Base change of `AdjoinRoot (fA n u)` from `A` to `K`: Mathlib's `AdjoinRoot.tensorAlgEquiv`,
-- with the coefficients moved along `K ⊗[A] A ≃ K`.
private noncomputable def tensorEquiv (n : ℕ) (u : A) :
    AdjoinRoot (fA n u) ⊗[A] K ≃ₐ[A] AdjoinRoot (fK K n u) :=
  (Algebra.TensorProduct.comm A (AdjoinRoot (fA n u)) K).trans
    (((AdjoinRoot.tensorAlgEquiv (T := K) (fA n u) _ rfl).trans
      (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid A K K) _ (fK K n u) (by
        rw [Polynomial.map_map]
        simp [Algebra.smul_def]))).restrictScalars A)

omit [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] in
private theorem tensorEquiv_root (n : ℕ) (u : A) :
    tensorEquiv (K := K) n u (AdjoinRoot.root (fA n u) ⊗ₜ[A] (1 : K)) =
      AdjoinRoot.root (fK K n u) := by
  rw [tensorEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    AlgEquiv.restrictScalars_apply, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

private theorem integralClosure_eq_adjoin (n : ℕ) (u : A) (hn : IsUnit ((n : ℕ) : A)) (hu : IsUnit
  u) :
    integralClosure A (AdjoinRoot (fK K n u)) = Algebra.adjoin A {AdjoinRoot.root (fK K n u)} := by
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn

  have hE : Algebra.Etale A (AdjoinRoot (fA n u)) :=
    (AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n u hn hu).1
  haveI : Algebra.Smooth A (AdjoinRoot (fA n u)) :=
    (Algebra.Etale.iff_formallyUnramified_and_smooth.mp hE).2
  apply le_antisymm
  ·
    intro x hx
    have hx' : IsIntegral A x := hx
    have h1 : IsIntegral A ((tensorEquiv (K := K) n u).symm x) := hx'.map (tensorEquiv n u).symm
    have h2 : IsIntegral (AdjoinRoot (fA n u)) ((tensorEquiv (K := K) n u).symm x) :=
      h1.tower_top
    obtain ⟨s, hs⟩ := mem_range_includeLeft_of_isIntegral (A := A) (K := K) _ h2
    rw [Algebra.TensorProduct.includeLeftRingHom_apply] at hs
    have hrange : ((tensorEquiv (K := K) n u).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (S := A))).range =
        Algebra.adjoin A {AdjoinRoot.root (fK K n u)} := by
      rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        AlgEquiv.toAlgHom_apply, tensorEquiv_root]
    change x ∈ (Algebra.adjoin A {AdjoinRoot.root (fK K n u)} : Subalgebra A _)
    rw [← hrange]
    refine ⟨s, ?_⟩
    change tensorEquiv (K := K) n u (s ⊗ₜ[A] (1 : K)) = x
    rw [hs, AlgEquiv.apply_symm_apply]
  ·
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    change IsIntegral A (AdjoinRoot.root (fK K n u))
    refine ⟨fA n u, Polynomial.monic_X_pow_sub_C u hn0, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, root_fK_pow, sub_self]

end KummerIntegralClosureKa

open KummerIntegralClosureKa in
private theorem integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit_aux
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (n : ℕ) (u : A) (hn : IsUnit (n : A)) (hu : IsUnit u) :
    integralClosure A (AdjoinRoot (X ^ n - C (algebraMap A K u) : K[X])) =
      Algebra.adjoin A {AdjoinRoot.root (X ^ n - C (algebraMap A K u) : K[X])} :=
  integralClosure_eq_adjoin n u hn hu


set_option autoImplicit false

open Polynomial

namespace KummerLocalKb

variable {B F : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Field F] [Algebra B F] [IsFractionRing B F]

variable (F) in

private noncomputable abbrev fv (k : ℕ) (v : B) : F[X] := X ^ k - C (algebraMap B F v)

private noncomputable abbrev fg (k : ℕ) (g : F) : F[X] := X ^ k - C g

private theorem root_fv_pow (k : ℕ) (v : B) :
    (AdjoinRoot.root (fv F k v)) ^ k = algebraMap F (AdjoinRoot (fv F k v)) (algebraMap B F v) := by
  have h := AdjoinRoot.eval₂_root (fv F k v)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

private theorem root_fg_pow (k : ℕ) (g : F) :
    (AdjoinRoot.root (fg k g)) ^ k = algebraMap F (AdjoinRoot (fg k g)) g := by
  have h := AdjoinRoot.eval₂_root (fg k g)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

section Twist

variable (k : ℕ) (v : B) (h : F) (g : F)

private noncomputable def α (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    AdjoinRoot (fv F k v) →ₐ[F] AdjoinRoot (fg k g) :=
  AdjoinRoot.liftAlgHom (fv F k v) (Algebra.ofId F (AdjoinRoot (fg k g)))
    (algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g)) (by
      change (fv F k v).eval₂ (algebraMap F (AdjoinRoot (fg k g))) _ = 0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
      rw [mul_pow, root_fg_pow, ← map_pow, ← map_mul]
      congr 1
      rw [hg, inv_pow, ← mul_assoc, mul_comm (h ^ k)⁻¹, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero k hh), mul_one])

private noncomputable def β (hg : g = algebraMap B F v * h ^ k) :
    AdjoinRoot (fg k g) →ₐ[F] AdjoinRoot (fv F k v) :=
  AdjoinRoot.liftAlgHom (fg k g) (Algebra.ofId F (AdjoinRoot (fv F k v)))
    (algebraMap F (AdjoinRoot (fv F k v)) h * AdjoinRoot.root (fv F k v)) (by
      change (fg k g).eval₂ (algebraMap F (AdjoinRoot (fv F k v))) _ = 0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
      rw [mul_pow, root_fv_pow, ← map_pow, ← map_mul, hg, mul_comm])

private theorem α_root (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    α k v h g hh hg (AdjoinRoot.root (fv F k v)) =
      algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g) := by
  simp [α]

private theorem β_root (hg : g = algebraMap B F v * h ^ k) :
    β k v h g hg (AdjoinRoot.root (fg k g)) =
      algebraMap F (AdjoinRoot (fv F k v)) h * AdjoinRoot.root (fv F k v) := by
  simp [β]

private noncomputable def τ (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    AdjoinRoot (fv F k v) ≃ₐ[F] AdjoinRoot (fg k g) :=
  AlgEquiv.ofAlgHom (α k v h g hh hg) (β k v h g hg)
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, β_root, map_mul, AlgHom.commutes, α_root, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hh, map_one, one_mul, AlgHom.coe_id, id_eq])
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, α_root, map_mul, AlgHom.commutes, β_root, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hh, map_one, one_mul, AlgHom.coe_id, id_eq])

private theorem τ_root (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    τ k v h g hh hg (AdjoinRoot.root (fv F k v)) =
      algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g) := by
  simp [τ, α_root]

end Twist


private theorem integralClosure_eq_adjoin_of_eq_mul_pow_aux
    (k : ℕ) (hk : IsUnit ((k : ℕ) : B)) (v : B) (hv : IsUnit v) (h : F) (hh : h ≠ 0)
    (g : F) (hg : g = algebraMap B F v * h ^ k) :
    integralClosure B (AdjoinRoot (fg k g)) =
      Algebra.adjoin B {algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g)} := by
  have hKa : integralClosure B (AdjoinRoot (fv F k v)) =
      Algebra.adjoin B {AdjoinRoot.root (fv F k v)} :=
    integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit_aux k v hk hv
  set τB : AdjoinRoot (fv F k v) ≃ₐ[B] AdjoinRoot (fg k g) := (τ k v h g hh hg).restrictScalars B
  have hτB_root : τB (AdjoinRoot.root (fv F k v)) =
      algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g) := τ_root k v h g hh hg
  rw [← integralClosure_map_algEquiv τB, hKa, AlgHom.map_adjoin_singleton]
  change Algebra.adjoin B {τB (AdjoinRoot.root (fv F k v))} = _
  rw [hτB_root]

end KummerLocalKb


set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open TopologicalSpace Opposite

namespace KummerChart

variable {X : Scheme.{u}} [IsIntegral X]

private theorem genericPoint_mem (V : X.Opens) [hV : Nonempty V] : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

private theorem preimage_eq_top {A : CommRingCat.{u}} (φ : X.functionField ⟶ A) (V : X.Opens) [hV
  : Nonempty V] :
    (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V = ⊤ := by
  apply top_le_iff.mp
  intro p _
  change (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)) p ∈ V
  have hmem : (X.fromSpecStalk (genericPoint X)) ((Spec.map φ) p) ∈
      Set.range (X.fromSpecStalk (genericPoint X)) := Set.mem_range_self _
  rw [Scheme.range_fromSpecStalk] at hmem
  rw [Scheme.Hom.comp_apply]
  exact hmem.mem_open V.isOpen (genericPoint_mem V)

private theorem app_eq {A : CommRingCat.{u}} (φ : X.functionField ⟶ A) (V : X.Opens) [hV :
  Nonempty V] :
    (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)).app V =
      X.presheaf.germ V (genericPoint X) (genericPoint_mem V) ≫ φ ≫ (Scheme.ΓSpecIso A).inv ≫
        (Spec A).presheaf.map (homOfLE (le_top :
          (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V ≤ ⊤)).op := by
  rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app (genericPoint_mem V)]
  simp only [Category.assoc]
  have hnat := (Spec.map φ).naturality
    (homOfLE (le_top : (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V ≤ ⊤)).op
  rw [Quiver.Hom.unop_op] at hnat
  erw [hnat]
  have h2 : (Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).app ⊤ = φ ≫ (Scheme.ΓSpecIso A).inv :=
    (Scheme.ΓSpecIso_inv_naturality φ).symm
  rw [← Category.assoc (Scheme.ΓSpecIso _).inv, h2]
  erw [Category.assoc]
  rfl

section KummerAlgebra

variable (k : ℕ) (g : X.functionField)

private abbrev KA : Type u := AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial
  X.functionField)

private noncomputable abbrev φK : X.functionField ⟶ CommRingCat.of (KA k g) :=
  CommRingCat.ofHom (algebraMap X.functionField (KA k g))

private noncomputable abbrev fK : Spec (CommRingCat.of (KA k g)) ⟶ X :=
  Spec.map (φK k g) ≫ X.fromSpecStalk (genericPoint X)

private noncomputable def secIso (V : X.Opens) [Nonempty V] :
    Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V) ≅ CommRingCat.of (KA k g) :=
  (Spec (CommRingCat.of (KA k g))).presheaf.mapIso (eqToIso (preimage_eq_top (φK k g) V).symm).op ≪≫
    Scheme.ΓSpecIso _

private theorem secIso_inv (V : X.Opens) [Nonempty V] :
    (secIso k g V).inv = (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv ≫
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE (le_top : (fK k g) ⁻¹ᵁ V ≤ ⊤)).op := by
  simp only [secIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv]
  congr 2

private theorem secIso_hom (V : X.Opens) [Nonempty V] :
    (secIso k g V).hom = (Spec (CommRingCat.of (KA k g))).presheaf.map
        (homOfLE (le_of_eq (preimage_eq_top (φK k g) V).symm) : ⊤ ⟶ (fK k g) ⁻¹ᵁ V).op ≫
      (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).hom := by
  simp only [secIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
  congr 2

private theorem secIso_hom_app (V : X.Opens) [Nonempty V] (r : Γ(X, V)) :
    (secIso k g V).hom (((fK k g).app V) r) = algebraMap X.functionField (KA k g)
      (X.germToFunctionField V r) := by
  have h1 : ((fK k g).app V) r = (secIso k g V).inv (algebraMap X.functionField (KA k g)
    (X.germToFunctionField V r)) := by
    rw [secIso_inv]
    change ((fK k g).app V) r = ((φK k g) ≫ (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv ≫
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE (le_top : (fK k g) ⁻¹ᵁ V ≤ ⊤)).op)
        (X.germToFunctionField V r)
    rw [← ConcreteCategory.comp_apply]
    erw [app_eq (φK k g) V]
  rw [h1, ← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  rfl

private theorem secIso_hom_res {V V' : X.Opens} [Nonempty V] [Nonempty V'] (i : (fK k g) ⁻¹ᵁ V' ⟶
  (fK k g) ⁻¹ᵁ V)
    (z : Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V)) :
    (secIso k g V').hom ((Spec (CommRingCat.of (KA k g))).presheaf.map i.op z) = (secIso k g
      V).hom z := by
  have hc : (Spec (CommRingCat.of (KA k g))).presheaf.map i.op ≫ (Spec (CommRingCat.of (KA k
    g))).presheaf.map
      (homOfLE (le_of_eq (preimage_eq_top (φK k g) V').symm) : ⊤ ⟶ (fK k g) ⁻¹ᵁ V').op =
      (Spec (CommRingCat.of (KA k g))).presheaf.map
        (homOfLE (le_of_eq (preimage_eq_top (φK k g) V).symm) : ⊤ ⟶ (fK k g) ⁻¹ᵁ V).op := by
    rw [← Functor.map_comp]; rfl
  rw [secIso_hom, secIso_hom, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply ((Spec (CommRingCat.of (KA k g))).presheaf.map i.op), hc]

private noncomputable def secAlgEquiv (V : X.Opens) [Nonempty V] :
    letI := ((fK k g).app V).hom.toAlgebra
    Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V) ≃ₐ[Γ(X, V)] KA k g :=
  letI := ((fK k g).app V).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := (secIso k g V).commRingCatIsoToRingEquiv) (fun r => by
    change (secIso k g V).hom (((fK k g).app V) r) = _
    rw [secIso_hom_app, IsScalarTower.algebraMap_apply Γ(X, V) X.functionField (KA k g)]
    rfl)

private theorem secAlgEquiv_apply (V : X.Opens) [Nonempty V] (z : Γ(Spec (CommRingCat.of (KA k
  g)), (fK k g) ⁻¹ᵁ V)) :
    letI := ((fK k g).app V).hom.toAlgebra
    secAlgEquiv k g V z = (secIso k g V).hom z := rfl

end KummerAlgebra

private theorem map_map {Z : Scheme.{u}} {A B C : Z.Opens} (i : B ⟶ A) (j : C ⟶ B) (l : C ⟶ A) (s
  : Γ(Z, A)) :
    Z.presheaf.map j.op (Z.presheaf.map i.op s) = Z.presheaf.map l.op s := by
  have hl : j ≫ i = l := Subsingleton.elim _ _
  rw [← hl, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

section Yside

variable (k : ℕ) (g : X.functionField)

private theorem root_pow : (AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g : Polynomial
  X.functionField)) ^ k =
    algebraMap X.functionField (KA k g) g := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  rw [h]; rfl

private noncomputable def yval (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) :
    Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) →+* KA k g :=
  letI := ((fK k g).app V).hom.toAlgebra
  ((secIso k g V).hom.hom.comp
    (integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V)).val.toRingHom).comp
    ((fK k g).normalizationObjIso hV).hom.hom

private theorem yval_apply (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) :
    letI := ((fK k g).app V).hom.toAlgebra
    yval k g V hV s = (secIso k g V).hom (((fK k g).normalizationObjIso hV).hom s).val := rfl

private theorem yval_injective (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) :
  Function.Injective (yval k g V hV) := by
  letI := ((fK k g).app V).hom.toAlgebra
  intro s s' hss'
  rw [yval_apply, yval_apply] at hss'
  have h1 := (secIso k g V).commRingCatIsoToRingEquiv.injective hss'
  have h2 := Subtype.val_injective h1
  exact ((fK k g).normalizationObjIso hV).commRingCatIsoToRingEquiv.injective h2

private theorem preimage_toNormalization (V : X.Opens) :
    (fK k g).toNormalization ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V) = (fK k g) ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]

private theorem yval_eq_appLE (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) :
    yval k g V hV s = (secIso k g V).hom ((fK k g).toNormalization.appLE ((fK k
      g).fromNormalization ⁻¹ᵁ V)
      ((fK k g) ⁻¹ᵁ V) (preimage_toNormalization k g V).ge s) := by
  letI := ((fK k g).app V).hom.toAlgebra
  rw [yval_apply, ← (fK k g).normalizationObjIso_hom_val hV]
  rfl

private theorem yval_res {V V' : X.Opens} [Nonempty V] [Nonempty V'] (hV : IsAffineOpen V) (hV' :
  IsAffineOpen V')
    (i : (fK k g).fromNormalization ⁻¹ᵁ V' ⟶ (fK k g).fromNormalization ⁻¹ᵁ V)
    (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) :
    yval k g V' hV' (((fK k g).normalization).presheaf.map i.op s) = yval k g V hV s := by
  have hi : (fK k g) ⁻¹ᵁ V' ≤ (fK k g) ⁻¹ᵁ V := by
    rw [preimage_eq_top, preimage_eq_top]
  rw [yval_eq_appLE, yval_eq_appLE,
    ← ConcreteCategory.comp_apply (((fK k g).normalization).presheaf.map i.op),
    Scheme.Hom.map_appLE,
      ← Scheme.Hom.appLE_map _ (preimage_toNormalization k g V).ge (homOfLE hi).op,
    ConcreteCategory.comp_apply, secIso_hom_res]

private theorem normalizationObjIso_hom_app (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) (r :
  Γ(X, V)) :
    letI := ((fK k g).app V).hom.toAlgebra
    ((fK k g).normalizationObjIso hV).hom ((fK k g).fromNormalization.app V r) =
      algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)),
        (fK k g) ⁻¹ᵁ V)) r := by
  letI := ((fK k g).app V).hom.toAlgebra
  rw [(fK k g).fromNormalization_app hV]
  change (((fK k g).normalizationObjIso hV).inv ≫ ((fK k g).normalizationObjIso hV).hom)
    (algebraMap _ _ r) = _
  rw [Iso.inv_hom_id]
  rfl

private theorem yval_app (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) (r : Γ(X, V)) :
    yval k g V hV ((fK k g).fromNormalization.app V r) = algebraMap X.functionField (KA k g)
      (X.germToFunctionField V r) := by
  letI := ((fK k g).app V).hom.toAlgebra
  have h1 : ((fK k g).normalizationObjIso hV).hom ((fK k g).fromNormalization.app V r) =
      algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)),
        (fK k g) ⁻¹ᵁ V)) r := by
    rw [(fK k g).fromNormalization_app hV]
    change (((fK k g).normalizationObjIso hV).inv ≫ ((fK k g).normalizationObjIso hV).hom)
      (algebraMap _ _ r) = _
    rw [Iso.inv_hom_id]
    rfl
  rw [yval_apply, h1, ← secIso_hom_app]
  rfl

private theorem exists_yval_eq_root (hk : k ≠ 0) (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
  (h : X.functionField)
    (uV : Γ(X, V)) (huV : X.germToFunctionField V uV = g / h ^ k) :
    ∃ T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V),
      yval k g V hV T = algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ := by
  letI := ((fK k g).app V).hom.toAlgebra
  set e := secAlgEquiv k g V with he
  set ρ : KA k g := algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ with hρ
  have hρk : ρ ^ k = algebraMap X.functionField (KA k g) (g / h ^ k) := by
    rw [hρ, mul_pow, root_pow, ← map_pow, ← map_mul, div_eq_mul_inv, mul_comm, inv_pow]
  have hint : IsIntegral Γ(X, V) (e.symm ρ) := by
    refine ⟨Polynomial.X ^ k - Polynomial.C uV, Polynomial.monic_X_pow_sub_C uV hk, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero, ← map_pow,
      hρk, ← huV]
    apply e.injective
    rw [e.apply_symm_apply, e.commutes, IsScalarTower.algebraMap_apply Γ(X,
      V) X.functionField (KA k g)]
    rfl
  refine ⟨((fK k g).normalizationObjIso hV).inv ⟨e.symm ρ, hint⟩, ?_⟩
  rw [yval_apply, ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  change e (e.symm ρ) = ρ
  exact e.apply_symm_apply ρ

end Yside

section Alg

variable (k : ℕ) (g : X.functionField)

private theorem isIntegrallyClosed_sections (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed Γ(X, V) := by
  letI (y : PrimeSpectrum Γ(X, V)) : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have hloc (P : Ideal Γ(X, V)) [hP : P.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP⟩)) P :=
    hV.isLocalization_stalk' ⟨P, hP⟩ (hV.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (Rₚ := fun P _ => X.presheaf.stalk (hV.fromSpec ⟨P, inferInstance⟩)) (fun P _ => hnorm _)

private theorem yval_eq_of_toNormalization_app_eq (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) (ρ : KA k g)
    (hT : (fK k g).toNormalization.app ((fK k g).fromNormalization ⁻¹ᵁ V) T =
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv ρ)) :
    yval k g V hV T = ρ := by
  rw [yval_eq_appLE, Scheme.Hom.appLE, ConcreteCategory.comp_apply, hT, map_map _ _
    (homOfLE le_top : (fK k g) ⁻¹ᵁ V ⟶ ⊤), secIso_hom, ConcreteCategory.comp_apply,
    map_map _ _ (𝟙 _), op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
      Iso.inv_hom_id_apply]

end Alg

section UP

variable (k : ℕ) (g : X.functionField)

private theorem root_div_pow (h : X.functionField) :
    (algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _) ^ k = algebraMap X.functionField
      (KA k g) (g / h ^ k) := by
  rw [mul_pow, root_pow, ← map_pow, ← map_mul, div_eq_mul_inv, mul_comm, inv_pow]

private theorem comp_C_mul_X_comp {F : Type*} [Field F] (q : F[X]) (c : F) (hc : c ≠ 0) :
    (q.comp (Polynomial.C c⁻¹ * Polynomial.X)).comp (Polynomial.C c * Polynomial.X) = q := by
  rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    ← mul_assoc, ← Polynomial.C_mul,
    inv_mul_cancel₀ hc, Polynomial.C_1, one_mul, Polynomial.comp_X]

variable (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)

include hV in

private theorem mk_eq_zero_of_aeval_rho_eq_zero (hk : k ≠ 0) (h : X.functionField) (hh : h ≠ 0)
  (uV : Γ(X, V))
    (huV : X.germToFunctionField V uV = g / h ^ k) (p : Γ(X, V)[X])
    (hp : Polynomial.aeval (algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _) p = 0) :
    AdjoinRoot.mk (Polynomial.X ^ k - Polynomial.C uV) p = 0 := by
  haveI : IsFractionRing Γ(X,
    V) X.functionField := functionField_isFractionRing_of_isAffineOpen X V hV
  set ρ : KA k g := algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ with hρ
  set fu : Γ(X, V)[X] := Polynomial.X ^ k - Polynomial.C uV with hfu
  have hmon : fu.Monic := Polynomial.monic_X_pow_sub_C uV hk
  have hρroot : Polynomial.aeval ρ fu = 0 := by
    rw [hfu, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hρ, root_div_pow, ← huV,
      sub_eq_zero,
      IsScalarTower.algebraMap_apply Γ(X, V) X.functionField (KA k g)]
    rfl

  set q := p %ₘ fu with hq
  have hq0 : Polynomial.aeval ρ q = 0 := by rw [hq,
    Polynomial.aeval_modByMonic_eq_self_of_root hρroot, hp]
  have hqdeg : q.natDegree < k := by
    have h1 : q.degree < fu.degree := Polynomial.degree_modByMonic_lt p hmon
    rw [hfu, Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hk)] at h1
    by_cases hq00 : q = 0
    · rw [hq00, Polynomial.natDegree_zero]; exact Nat.pos_of_ne_zero hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hq00).mpr h1

  set qK : X.functionField[X] := q.map (algebraMap Γ(X, V) X.functionField) with hqK
  set q' : X.functionField[X] := qK.comp (Polynomial.C h⁻¹ * Polynomial.X) with hq'
  have hq'root : Polynomial.aeval (AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g :
    X.functionField[X])) q' = 0 := by
    rw [hq', Polynomial.aeval_comp, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, ← hρ, hqK,
      Polynomial.aeval_map_algebraMap, hq0]
  have hq'zero : q' = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hq'root
    refine Polynomial.eq_zero_of_dvd_of_natDegree_lt hq'root ?_
    rw [Polynomial.natDegree_X_pow_sub_C]
    calc q'.natDegree ≤ qK.natDegree * (Polynomial.C h⁻¹ * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
      _ ≤ qK.natDegree * 1 := by
          gcongr
          exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      _ ≤ q.natDegree := by rw [mul_one, hqK]; exact Polynomial.natDegree_map_le
      _ < k := hqdeg
  have hqKzero : qK = 0 := by
    rw [← comp_C_mul_X_comp qK h hh, ← hq', hq'zero, Polynomial.zero_comp]
  have hqzero : q = 0 := by
    apply Polynomial.map_injective (algebraMap Γ(X,
      V) X.functionField) (IsFractionRing.injective _ _)
    rw [← hqK, hqKzero, Polynomial.map_zero]

  have hpq : AdjoinRoot.mk fu p = AdjoinRoot.mk fu q := by
    rw [hq, AdjoinRoot.mk_eq_mk, Polynomial.modByMonic_eq_sub_mul_div p fu]
    exact ⟨p /ₘ fu, by ring⟩
  rw [hpq, hqzero, map_zero]

set_option maxHeartbeats 4000000 in

private theorem existsUnique_algHom (hnorm : ∀ x : X,
  IsIntegrallyClosed (X.presheaf.stalk x)) (hk : IsUnit ((k : ℕ) : Γ(X, V)))
    (uV : Γ(X, V)) (hu : IsUnit uV) (h : X.functionField) (hh : h ≠ 0)
    (huV : X.germToFunctionField V uV = g / h ^ k)
    (T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V))
    (hT : yval k g V hV T = algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _)
    (C : Type u) [CommRing C] [Algebra Γ(X, V) C] (c : C) (hc : c ^ k = algebraMap Γ(X, V) C uV) :
    letI := ((fK k g).fromNormalization.app V).hom.toAlgebra
    ∃! χ : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) →ₐ[Γ(X, V)] C, χ T = c := by
  letI algB := ((fK k g).fromNormalization.app V).hom.toAlgebra
  letI algS := ((fK k g).app V).hom.toAlgebra
  haveI : IsIntegrallyClosed Γ(X, V) := isIntegrallyClosed_sections V hV hnorm
  haveI : IsFractionRing Γ(X,
    V) X.functionField := functionField_isFractionRing_of_isAffineOpen X V hV
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, isUnit_zero_iff] at hk
    exact zero_ne_one hk
  set ρ : KA k g := algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ with hρ

  have hg : g = algebraMap Γ(X, V) X.functionField uV * h ^ k := by
    change g = X.germToFunctionField V uV * h ^ k
    rw [huV, div_mul_cancel₀ _ (pow_ne_zero _ hh)]
  have hIC := KummerLocalKb.integralClosure_eq_adjoin_of_eq_mul_pow_aux (B := Γ(X,
    V)) (F := X.functionField) k hk uV hu h hh g hg

  let Ψ₁ : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) ≃ₐ[Γ(X, V)]
      integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V) :=
    AlgEquiv.ofRingEquiv (f := ((fK k g).normalizationObjIso hV).commRingCatIsoToRingEquiv) (fun a
      =>
      normalizationObjIso_hom_app k g V hV a)
  let e := secAlgEquiv k g V
  let Ψ₂ : integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V) ≃ₐ[Γ(X, V)]
      integralClosure Γ(X, V) (KA k g) :=
    (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))
  let Ψ₃ : integralClosure Γ(X, V) (KA k g) ≃ₐ[Γ(X, V)] Algebra.adjoin Γ(X, V) {ρ} :=
    Subalgebra.equivOfEq _ _ hIC
  let Ψ := Ψ₁.trans (Ψ₂.trans Ψ₃)
  have hΨT : (Ψ T : KA k g) = ρ := (show (Ψ T : KA k g) = yval k g V hV T from rfl).trans hT

  obtain ⟨fu, hfu⟩ : ∃ fu : Γ(X, V)[X], fu = Polynomial.X ^ k - Polynomial.C uV := ⟨_, rfl⟩
  have hρk : ρ ^ k = algebraMap Γ(X, V) (KA k g) uV := by
    rw [hρ, root_div_pow, ← huV, IsScalarTower.algebraMap_apply Γ(X, V) X.functionField (KA k g)]
    rfl
  let ρ' : Algebra.adjoin Γ(X, V) {ρ} := ⟨ρ, Algebra.self_mem_adjoin_singleton Γ(X, V) ρ⟩
  have hρ'root : fu.eval₂ (algebraMap Γ(X, V) (Algebra.adjoin Γ(X, V) {ρ})) ρ' = 0 := by
    apply Subtype.ext
    rw [← Polynomial.aeval_def, Polynomial.aeval_subalgebra_coe]
    change Polynomial.aeval ρ fu = 0
    rw [Polynomial.aeval_def, hfu, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, hρk, sub_self]
  let θ : AdjoinRoot fu →ₐ[Γ(X, V)] Algebra.adjoin Γ(X, V) {ρ} :=
    AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) ρ' hρ'root
  have hθroot : θ (AdjoinRoot.root fu) = ρ' := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hθsurj : Function.Surjective θ := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    refine ⟨AdjoinRoot.mk fu p, Subtype.ext ?_⟩
    change ((AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) ρ' hρ'root (AdjoinRoot.mk fu p) :
      Algebra.adjoin Γ(X, V) {ρ}) : KA k g) = _
    change ((Polynomial.eval₂ (algebraMap Γ(X, V) (Algebra.adjoin Γ(X,
      V) {ρ})) ρ' p : Algebra.adjoin Γ(X, V) {ρ}) : KA k g) =
      Polynomial.aeval ρ p
    rw [← Polynomial.aeval_def, Polynomial.aeval_subalgebra_coe]
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using AdjoinRoot.induction_on with
    | ih p =>
      rw [hfu]
      apply mk_eq_zero_of_aeval_rho_eq_zero k g V hV hk0 h hh uV huV p
      have hx' := congrArg (fun y : Algebra.adjoin Γ(X, V) {ρ} => (y : KA k g)) hx
      change ((AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) ρ' hρ'root (AdjoinRoot.mk fu p) :
        Algebra.adjoin Γ(X, V) {ρ}) : KA k g) = 0 at hx'
      change ((Polynomial.eval₂ (algebraMap Γ(X, V) (Algebra.adjoin Γ(X,
        V) {ρ})) ρ' p : Algebra.adjoin Γ(X, V) {ρ}) : KA k g) = 0
        at hx'
      rw [← Polynomial.aeval_def, Polynomial.aeval_subalgebra_coe] at hx'
      exact hx'
  let Θ : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) ≃ₐ[Γ(X, V)] AdjoinRoot fu :=
    Ψ.trans (AlgEquiv.ofBijective θ ⟨hθinj, hθsurj⟩).symm
  have hΘT : Θ T = AdjoinRoot.root fu := by
    change (AlgEquiv.ofBijective θ ⟨hθinj, hθsurj⟩).symm (Ψ T) = _
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [hΨT]
    change ρ = ((θ (AdjoinRoot.root fu) : Algebra.adjoin Γ(X, V) {ρ}) : KA k g)
    rw [hθroot]

  have hcroot : fu.eval₂ (algebraMap Γ(X, V) C) c = 0 := by
    rw [hfu, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hc, sub_self]
  refine ⟨(AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) c hcroot).comp Θ.toAlgHom, ?_, ?_⟩
  · change AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) c hcroot (Θ T) = c
    rw [hΘT]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  · intro χ hχ
    have key : χ.comp Θ.symm.toAlgHom = AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) c hcroot := by
      apply AdjoinRoot.algHom_ext
      rw [show (AdjoinRoot.liftAlgHom fu (Algebra.ofId _ _) c hcroot)
          (AdjoinRoot.root fu) = c from AdjoinRoot.liftAlgHom_root _ _ _ _,
        AlgHom.comp_apply]
      change χ (Θ.symm (AdjoinRoot.root fu)) = c
      rw [← hΘT, Θ.symm_apply_apply, hχ]
    rw [← key]
    ext x
    change χ x = χ (Θ.symm (Θ x))
    rw [Θ.symm_apply_apply]

end UP

section Geom

variable (k : ℕ) (g : X.functionField)

private theorem algebraMap_germ (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) =
      @Scheme.germToFunctionField X _ U ⟨⟨x, hx⟩⟩ s := by
  rw [RingHom.algebraMap_toAlgebra]
  change (X.presheaf.germ U x hx ≫ X.presheaf.stalkSpecializes _) s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

omit [IsIntegral X] in
private theorem appLE_eq_of_eq {Z Z' : Scheme.{u}} {f₁ f₂ : Z' ⟶ Z} (e : f₁ = f₂) (U : Z.Opens) (W
  : Z'.Opens)
    (h₁ : W ≤ f₁ ⁻¹ᵁ U) (h₂ : W ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U W h₁ = f₂.appLE U W h₂ := by
  subst e; rfl

omit [IsIntegral X] in
private theorem appLE_top_top {Z Z' : Scheme.{u}} (f : Z' ⟶ Z) (e : (⊤ : Z'.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  have h : e = le_top := Subsingleton.elim _ _
  rw [h]
  exact f.appLE_eq_app

omit [IsIntegral X] in

private theorem fromSpec_appLE_top {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U) (e : (⊤ :
  (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

omit [IsIntegral X] in

private theorem eq_toSpecΓ_SpecMap_appLE_fromSpec {Z : Scheme.{u}} (z : Z ⟶ X) (V : X.Opens) (hV :
  IsAffineOpen V)
    (hz : z ⁻¹ᵁ V = ⊤) : z = Z.toSpecΓ ≫ Spec.map (z.appLE V ⊤ hz.ge) ≫ hV.fromSpec := by
  have h1 := Scheme.Opens.toSpecΓ_SpecMap_appLE z V ⊤ hz.ge
  have h2 : (⊤ : Z.Opens).toSpecΓ ≫ Spec.map (z.appLE V ⊤ hz.ge) ≫ hV.fromSpec = (⊤ : Z.Opens).ι ≫
    z := by
    rw [← Category.assoc, h1, Category.assoc, IsAffineOpen.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [Scheme.Opens.toSpecΓ_top, Category.assoc] at h2
  rw [← Scheme.topIso_hom] at h2
  exact ((cancel_epi Z.topIso.hom).mp h2).symm

end Geom

end KummerChart

set_option maxHeartbeats 8000000 in
open KummerChart in
/-- **Local universal property of a normalized Kummer cover.**

Let `X` be a normal integral scheme with function field `K`, `V` a nonempty affine open, `k` a
natural number invertible on `V`, `h ≠ 0` an element of `K`, and `u` a unit on `V` whose germ
at every point of `V` maps to `g / h ^ k` in `K`. Let `Y` be the normalization of `X` in
`Spec K[t]/(t ^ k - g)`, with structure map `π : Y ⟶ X`, and let `ρ` be the class of `t`.
Take a section `T` of `Y` over `π ⁻¹ᵁ V` whose pullback along `Spec K[t]/(t ^ k - g) ⟶ Y` is
the restriction of `h⁻¹ * ρ`: the root normalized so that its `k`-th power is `g / h ^ k`, the
image of `u`, and not `g`. Then a morphism `z : Z ⟶ X` with `z ⁻¹ᵁ V = ⊤`, together with a
global section `τ` of `Z` whose restriction to `z ⁻¹ᵁ V` has `k`-th power `z.app V u`, lifts to
a unique `s : Z ⟶ Y` with `s ≫ π = z` such that `s.app (π ⁻¹ᵁ V) T` is the restriction of
`τ`. -/
public theorem AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen
    {X : Scheme.{u}} [IsIntegral X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (g : X.functionField)
    (V : X.Opens) (hV : IsAffineOpen V) (hVne : Nonempty V) (hk : IsUnit ((k : ℕ) : Γ(X, V)))
    (u : Γ(X, V)) (hu : IsUnit u) (h : X.functionField) (hh : h ≠ 0)
    (hval : ∀ (x : X) (hx : x ∈ V),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hx u) = g / h ^ k) :
    let A' := AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField A')) ≫ X.fromSpecStalk
      (genericPoint X)
    let π := f₀.fromNormalization
    let Y := f₀.normalization
    ∀ T : Γ(Y, π ⁻¹ᵁ V),
      f₀.toNormalization.app (π ⁻¹ᵁ V) T =
        (Spec (CommRingCat.of A')).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (algebraMap X.functionField A' h⁻¹ *
            AdjoinRoot.root _)) →
      ∀ (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ V = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app V u →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ := by
  intro A' f₀ π Y T hT Z z hz τ hτ
  haveI := hVne
  change ∃! s : Z ⟶ (fK k g).normalization, s ≫ (fK k g).fromNormalization = z ∧
      s.app ((fK k g).fromNormalization ⁻¹ᵁ V) T = Z.presheaf.map (homOfLE le_top).op τ
  have hT' : (fK k g).toNormalization.app ((fK k g).fromNormalization ⁻¹ᵁ V) T =
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv (algebraMap X.functionField (KA k g) h⁻¹
          * AdjoinRoot.root _)) := hT
  clear hT
  have hρ := yval_eq_of_toNormalization_app_eq k g V hV T _ hT'

  have huV : X.germToFunctionField V u = g / h ^ k := by
    obtain ⟨⟨x, hx⟩⟩ := hVne
    rw [← algebraMap_germ V x hx u]
    exact hval x hx

  letI algB : Algebra Γ(X, V) Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) :=
    ((fK k g).fromNormalization.app V).hom.toAlgebra
  letI algC : Algebra Γ(X, V) Γ(Z, ⊤) := (z.appLE V ⊤ hz.ge).hom.toAlgebra
  have hτ' : τ ^ k = algebraMap Γ(X, V) Γ(Z, ⊤) u := by
    have h1 := congrArg (Z.presheaf.map (homOfLE hz.ge).op) hτ
    rw [map_pow, map_map _ _ (𝟙 _), op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply] at h1
    exact h1
  obtain ⟨χ, hχT, hχuniq⟩ := existsUnique_algHom k g V hV hnorm hk u hu h hh huV T hρ Γ(Z, ⊤) τ hτ'
  have hχA : ∀ a : Γ(X, V),
    χ ((fK k g).fromNormalization.app V a) = z.appLE V ⊤ hz.ge a := fun a => χ.commutes a
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) ⟶ Γ(Z, ⊤),
      φ = CommRingCat.ofHom χ.toRingHom := ⟨_, rfl⟩
  have hφA : (fK k g).fromNormalization.app V ≫ φ = z.appLE V ⊤ hz.ge := by
    rw [hφ]
    ext a
    exact hχA a
  have hπV : IsAffineOpen ((fK k g).fromNormalization ⁻¹ᵁ V) := hV.preimage _

  have F1 : hπV.fromSpec ≫ (fK k g).fromNormalization = Spec.map ((fK k g).fromNormalization.app
    V) ≫ hV.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec (fK k g).fromNormalization hV hπV le_rfl,
      Scheme.Hom.appLE_eq_app]
  have F2 := eq_toSpecΓ_SpecMap_appLE_fromSpec z V hV hz

  have F3 : ∀ φ' : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) ⟶ Γ(Z, ⊤),
      (Z.toSpecΓ ≫ Spec.map φ').appTop = (Scheme.ΓSpecIso _).hom ≫ φ' := by
    intro φ'
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]

  have e₂ : (⊤ : (Spec Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)).Opens) ≤
      hπV.fromSpec ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V) := by rw
        [IsAffineOpen.fromSpec_preimage_self]
  have F4 : ∀ (t : Z ⟶ Spec Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V))
      (e : (⊤ : Z.Opens) ≤ (t ≫ hπV.fromSpec) ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V)),
      (t ≫ hπV.fromSpec).appLE ((fK k g).fromNormalization ⁻¹ᵁ V) ⊤ e = (Scheme.ΓSpecIso _).inv ≫
        t.appTop := by
    intro t e
    rw [← Scheme.Hom.appLE_comp_appLE t hπV.fromSpec ((fK k g).fromNormalization ⁻¹ᵁ V) ⊤ ⊤ e₂
      le_top,
      fromSpec_appLE_top hπV e₂]
    exact congrArg (fun φ => (Scheme.ΓSpecIso _).inv ≫ φ) (appLE_top_top t _)
  have hcomp : ((Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec) ≫ (fK k g).fromNormalization = z := by
    rw [Category.assoc, Category.assoc, F1, ← Spec.map_comp_assoc, hφA, ← F2]
  refine ⟨(Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec, ⟨hcomp, ?_⟩, ?_⟩
  ·
    have e : (⊤ : Z.Opens) ≤ ((Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec) ⁻¹ᵁ ((fK k
      g).fromNormalization ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, hcomp, hz]
    have happLE : ((Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec).appLE ((fK k g).fromNormalization ⁻¹ᵁ
      V) ⊤ e = φ := by
      rw [F4, F3, Iso.inv_hom_id_assoc]
    have hval : ((Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec).appLE ((fK k g).fromNormalization ⁻¹ᵁ V)
      ⊤ e T = τ := by
      rw [happLE, hφ]
      exact hχT
    rw [Scheme.Hom.appLE] at hval
    have htest : (Z.presheaf.map (homOfLE e).op)
        ((((Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec).app
          ((fK k g).fromNormalization ⁻¹ᵁ V)) T) = τ := hval
    have h2 := congrArg (Z.presheaf.map (homOfLE (le_top :
      ((Z.toSpecΓ ≫ Spec.map φ) ≫ hπV.fromSpec) ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V) ≤ ⊤)).op)
        htest
    rw [map_map _ _ (𝟙 _), op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at h2
    exact h2
  ·
    rintro s' ⟨h1', h2'⟩
    have hrange : Set.range s' ⊆ Set.range hπV.fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      change (fK k g).fromNormalization (s' x) ∈ V
      rw [← Scheme.Hom.comp_apply, h1']
      have : x ∈ z ⁻¹ᵁ V := by rw [hz]; trivial
      exact this
    obtain ⟨t', ht'⟩ : ∃ t' : Z ⟶ Spec Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V),
        t' ≫ hπV.fromSpec = s' :=
      ⟨IsOpenImmersion.lift hπV.fromSpec s' hrange, IsOpenImmersion.lift_fac _ _ _⟩

    obtain ⟨φ', hφ'def⟩ : ∃ φ' : Γ((fK k g).normalization,
      (fK k g).fromNormalization ⁻¹ᵁ V) ⟶ Γ(Z, ⊤),
        φ' = (Scheme.ΓSpecIso _).inv ≫ t'.appTop := ⟨_, rfl⟩
    have e' : (⊤ : Z.Opens) ≤ s' ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, h1', hz]
    have hs'appLE : s'.appLE ((fK k g).fromNormalization ⁻¹ᵁ V) ⊤ e' = φ' := by
      rw [hφ'def, ← F4 t' (by rw [ht']; exact e')]
      exact appLE_eq_of_eq ht'.symm _ _ _ _
    have hφ'A : ∀ a : Γ(X, V), φ' ((fK k g).fromNormalization.app V a) = z.appLE V ⊤ hz.ge a := by
      intro a
      rw [← hs'appLE, ← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE]
      rw [appLE_eq_of_eq h1' V ⊤ _ hz.ge]
    have hφ'T : φ' T = τ := by
      rw [← hs'appLE, Scheme.Hom.appLE]
      have hsplit : (Z.presheaf.map (homOfLE e').op)
          ((s'.app ((fK k g).fromNormalization ⁻¹ᵁ V)) T) = τ := by
        rw [h2', map_map _ _ (𝟙 _), op_id, CategoryTheory.Functor.map_id,
          ConcreteCategory.id_apply]
      exact hsplit
    let χ' : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) →ₐ[Γ(X, V)] Γ(Z, ⊤) :=
      { φ'.hom with commutes' := fun a => hφ'A a }
    have hχ' : χ' = χ := hχuniq χ' hφ'T
    have hφφ' : φ' = φ := by
      rw [hφ]
      ext x
      change χ' x = χ x
      rw [hχ']

    have ht'eq : t' = Z.toSpecΓ ≫ Spec.map φ := by
      apply ext_of_isAffine
      rw [F3, ← hφφ', hφ'def, Iso.hom_inv_id_assoc]
    rw [← ht', ht'eq]
