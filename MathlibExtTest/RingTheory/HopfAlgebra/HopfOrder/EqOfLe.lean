/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.HopfOrder.EqOfLe
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

universe u v w w'

open scoped TensorProduct

/-- Exact source statement of the target theorem, with the original binders. -/
example
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type w'} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    {S S' : Subalgebra R A} (hle : S ≤ S')
    (hSfin : Module.Finite R ↥S)
    (hSspan : Submodule.span K (S : Set A) = ⊤)
    (hScomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hSanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hScounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hS'fin : Module.Finite R ↥S')
    (hS'span : Submodule.span K (S' : Set A) = ⊤)
    (hS'comul : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S'.val)).range)
    (hS'anti : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hS'counit : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker : S.comap
        (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
      = S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars
          R))
    (himg : S.map ((π : A →ₐ[K] Ā).restrictScalars R) = S'.map
        ((π : A →ₐ[K] Ā).restrictScalars R)) :
    S = S' :=
  HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq hle hSfin hSspan hScomul hSanti hScounit
    hS'fin hS'span hS'comul hS'anti hS'counit π hπ hker himg

/-- Exact source statement: images of Hopf orders. -/
example
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π) :
    Module.Finite R ↥((S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    Submodule.span K (((S.map ((π : A →ₐ[K] Ā).restrictScalars R)) : Subalgebra R Ā) : Set Ā) = ⊤ ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp
              ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp
              ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), HopfAlgebra.antipode K (A := Ā) x ∈
        (S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.counit (R := K) (A := Ā) x ∈
        (algebraMap R K).range) :=
  HopfOrder.isHopfOrder_map S hfin hspan hcomul hanti hcounit π hπ

/-- Exact source statement: Hopf kernels of integral maps. -/
example
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Free R H]
    (e : H →ₐ[R] A) (he : Function.Injective e) (heS : e.range = S)
    (he_comul : ∀ h : H, Coalgebra.comul (R := K) (e h) =
        Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (Coalgebra.comul (R := R) h))
    (π : A →ₐc[K] Ā)
    {Hbar : Type*} [CommRing Hbar] [HopfAlgebra R Hbar] [Module.Free R Hbar]
    (q : H →ₐc[R] Hbar) (ebar : Hbar →ₐ[R] Ā) (hebar : Function.Injective ebar)
    (hsq : ∀ h : H, ebar (q h) = π (e h)) :
    (HopfAlgebra.hopfKer q).map e = S ⊓ (HopfAlgebra.hopfKer π).restrictScalars R :=
  HopfOrder.map_hopfKer_eq_inf_hopfKer S e he heS he_comul π q ebar hebar hsq

/-- Exact source statement: surjections onto finite free Hopf algebras are Hopf-Galois. -/
example {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) : HopfAlgebra.IsHopfGalois π :=
  HopfAlgebra.isHopfGalois_of_surjective π hπ

/-- Exact source statement: finite projectivity over the Hopf kernel. -/
example {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Module.Finite ↥(HopfAlgebra.hopfKer π) A ∧ Module.Projective ↥(HopfAlgebra.hopfKer π) A :=
  HopfAlgebra.finite_projective_hopfKer_of_surjective π hπ

/-- Exact source statement: left integrals on a finite free Hopf algebra. -/
example {R : Type u} [CommRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
    [Module.Finite R B] [Module.Free R B] :
    ∃ (n : ℕ) (Λ : Fin n → Module.Dual R B) (u : Fin n → B),
      (∀ j (b : B), (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ j b) •
          (1 : B))
      ∧ ∀ b : B, ∑ j, Λ j (u j * b) = Coalgebra.counit b :=
  HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit

/-- Exact source statement: surjectivity of the canonical map. -/
example {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    {B : Type*} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Surjective (HopfAlgebra.canMap π) :=
  HopfAlgebra.canMap_surjective_of_surjective π hπ

/-! ### The Hopf order `ℤ[C₃]` in `ℚ[C₃]` -/

namespace HopfOrderTest

open MonoidAlgebra

/-- The cyclic group of order three, written multiplicatively. -/
private abbrev C₃ : Type := Multiplicative (ZMod 3)

/-- The group algebra `ℚ[C₃]`. -/
private abbrev QC₃ : Type := MonoidAlgebra ℚ C₃

/-- A generator of `C₃`. -/
private abbrev gen : C₃ := Multiplicative.ofAdd 1

/-- The basis element of `ℚ[C₃]` at the generator. -/
private noncomputable abbrev g : QC₃ := single gen 1

/-- The group ring `ℤ[C₃]`, as the `ℤ`-subalgebra of `ℚ[C₃]` generated by `g`. -/
private noncomputable abbrev S : Subalgebra ℤ QC₃ := Algebra.adjoin ℤ {g}

private theorem g_mem : g ∈ S := Algebra.subset_adjoin rfl

private theorem g_mul_g : g * g = single gen⁻¹ 1 := by
  rw [single_mul_single, mul_one]
  rfl

private theorem g_ne_one : g ≠ 1 := by
  rw [one_def]
  intro h
  exact absurd ((single_left_inj one_ne_zero).mp h) (by decide)

/-- The counit of `ℚ[C₃]` takes integer values on `ℤ[C₃]`: it is `1` at `g`. -/
private theorem hcounit : ∀ x ∈ S, Coalgebra.counit (R := ℚ) x ∈ (algebraMap ℤ ℚ).range := by
  intro x hx
  have h : S.map ((Bialgebra.counitAlgHom ℚ QC₃).restrictScalars ℤ) ≤ ⊥ := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    simp
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩))
  exact ⟨r, hr⟩

/-- The comultiplication of `ℚ[C₃]` maps `ℤ[C₃]` into the image of `ℤ[C₃] ⊗[ℤ] ℤ[C₃]`, since
`Δ g = g ⊗ g`. -/
private theorem hcomul : ∀ x ∈ S, Coalgebra.comul (R := ℚ) x ∈
    (Algebra.TensorProduct.productMap
      (((Algebra.TensorProduct.includeLeft : QC₃ →ₐ[ℚ] QC₃ ⊗[ℚ] QC₃).restrictScalars ℤ).comp S.val)
      (((Algebra.TensorProduct.includeRight : QC₃ →ₐ[ℚ] QC₃ ⊗[ℚ] QC₃).restrictScalars ℤ).comp
        S.val)).range := by
  intro x hx
  have h : S.map ((Bialgebra.comulAlgHom ℚ QC₃).restrictScalars ℤ) ≤
      (HopfOrder.tensorSqHom (K := ℚ) S).range := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    rw [AlgHom.restrictScalars_apply, Bialgebra.comulAlgHom_apply,
      (isGroupLikeElem_single_one gen).comul_eq_tmul_self]
    exact HopfOrder.tmul_mem_range_tensorSqHom g_mem g_mem
  exact h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)

/-- `ℤ[C₃]` is stable under the antipode, which sends `g` to `g⁻¹ = g * g`. -/
private theorem hantipode : ∀ x ∈ S, HopfAlgebra.antipode ℚ (A := QC₃) x ∈ S := by
  intro x hx
  have h : S.map ((HopfAlgebra.antipodeAlgHom ℚ QC₃).restrictScalars ℤ) ≤ S := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    change HopfAlgebra.antipode ℚ g ∈ S
    rw [antipode_single, HopfAlgebra.antipode_one, ← g_mul_g]
    exact mul_mem g_mem g_mem
  exact h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem g_pow_three : g ^ 3 = 1 := by
  rw [single_pow, one_pow, one_def]
  rfl

/-- `ℤ[C₃]` is finite over `ℤ`, since `g ^ 3 = 1` makes `g` integral. -/
private instance hfin : Module.Finite ℤ S :=
  Algebra.finite_adjoin_simple_of_isIntegral
    (IsIntegral.of_pow three_pos (by rw [g_pow_three]; exact isIntegral_one))

private instance : Module.Flat ℤ S := HopfOrder.moduleFlat_of_finite (K := ℚ) S

private theorem single_mem (h : C₃) : single h (1 : ℚ) ∈ S := by
  have : h = gen ^ (Multiplicative.toAdd h).val := by revert h; decide
  rw [this, ← one_pow (M := ℚ) (Multiplicative.toAdd h).val, ← single_pow]
  exact pow_mem g_mem _

/-- `ℤ[C₃]` spans `ℚ[C₃]` over `ℚ`: it contains every group element. -/
private theorem hspan : Submodule.span ℚ (S : Set QC₃) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of h => exact Submodule.subset_span (single_mem h)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul r x hx => exact Submodule.smul_mem _ r hx

/-- The element `g` of `ℤ[C₃]`. -/
private noncomputable def gS : S := ⟨g, g_mem⟩

/-- Over the principal ideal domain `ℤ`, the finite subalgebra `ℤ[C₃]` is free. -/
example : Module.Free ℤ S := HopfOrder.moduleFree_of_finite (K := ℚ) S

/-- The counit of the Hopf order structure on `ℤ[C₃]` sends `g` to `1`, read through the
definition of the restricted counit. -/
example : letI := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    Coalgebra.counit (R := ℤ) gS = 1 := by
  change HopfOrder.counitS hcounit gS = 1
  apply IsFractionRing.injective ℤ ℚ
  refine (HopfOrder.exists_algebraMap_eq_counit hcounit gS).choose_spec.trans ?_
  simp [gS]

/-- The antipode of the Hopf order structure on `ℤ[C₃]` sends `g` to `g⁻¹ = g * g`, which is not
`g`. -/
example : letI := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    ((HopfAlgebra.antipode ℤ gS : S) : QC₃) = g * g := by
  change HopfAlgebra.antipode ℚ g = g * g
  rw [antipode_single, HopfAlgebra.antipode_one, g_mul_g]

/-- The comultiplication of the Hopf order structure on `ℤ[C₃]` sends `g` to an element of
`ℤ[C₃] ⊗[ℤ] ℤ[C₃]` whose image in `ℚ[C₃] ⊗[ℚ] ℚ[C₃]` is `g ⊗ g`, read through the definition of
the restricted comultiplication. -/
example : letI := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    HopfOrder.doubleCmp S (Coalgebra.comul (R := ℤ) gS) = g ⊗ₜ[ℚ] g := by
  change HopfOrder.doubleCmp S (HopfOrder.comulS hcomul gS) = g ⊗ₜ[ℚ] g
  exact (HopfOrder.exists_doubleCmp_eq_comul hcomul gS).choose_spec.trans
    (isGroupLikeElem_single_one gen).comul_eq_tmul_self

/-- The same through `HopfOrder.val_comul` and `HopfOrder.tensorSqHom`. -/
example : letI := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    HopfOrder.tensorSqHom S (Coalgebra.comul (R := ℤ) gS) = g ⊗ₜ[ℚ] g :=
  (HopfOrder.val_comul hcomul hcounit hantipode gS).symm.trans
    (isGroupLikeElem_single_one gen).comul_eq_tmul_self

/-- The hypotheses of the main theorem are satisfiable: they hold for `S = S' = ℤ[C₃]` in
`ℚ[C₃]` with `π` the identity. -/
example : S = S :=
  HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq le_rfl hfin hspan hcomul hantipode hcounit
    hfin hspan hcomul hantipode hcounit (BialgHom.id ℚ QC₃) Function.surjective_id rfl rfl

private theorem counit_surjective : Function.Surjective (Bialgebra.counitBialgHom ℚ QC₃) :=
  fun r => ⟨algebraMap ℚ QC₃ r, by simp⟩

/-- Through `HopfAlgebra.isHopfGalois_of_surjective` for the counit `ℚ[C₃] → ℚ`: the element
`g ⊗ 1 - 1 ⊗ g`, which the canonical map kills, lies in the span of the balancing relations. -/
example : g ⊗ₜ[ℚ] (1 : QC₃) - 1 ⊗ₜ[ℚ] g ∈
    Submodule.span ℚ (HopfAlgebra.balancingRelations (Bialgebra.counitBialgHom ℚ QC₃)) := by
  refine (HopfAlgebra.isHopfGalois_of_surjective _ counit_surjective).2 _ ?_
  rw [map_sub, HopfAlgebra.canMap_tmul_one, HopfAlgebra.canMap_one_tmul,
    HopfAlgebra.coaction_apply, (isGroupLikeElem_single_one gen).comul_eq_tmul_self,
    Algebra.TensorProduct.map_tmul]
  simp

/-- The identity of the finite free Hopf algebra `ℚ[C₃]` is Hopf–Galois. -/
example : HopfAlgebra.IsHopfGalois (BialgHom.id ℚ QC₃) :=
  HopfAlgebra.isHopfGalois_of_surjective _ Function.surjective_id

/-- `ℚ[C₃]` is finite projective over the Hopf kernel of its counit. -/
example : Module.Finite ↥(HopfAlgebra.hopfKer (Bialgebra.counitBialgHom ℚ QC₃)) QC₃ ∧
    Module.Projective ↥(HopfAlgebra.hopfKer (Bialgebra.counitBialgHom ℚ QC₃)) QC₃ :=
  HopfAlgebra.finite_projective_hopfKer_of_surjective _ counit_surjective

/-- The canonical map of the identity of `ℚ[C₃]` reaches `1 ⊗ g`. -/
example : ∃ w, HopfAlgebra.canMap (BialgHom.id ℚ QC₃) w = 1 ⊗ₜ[ℚ] g :=
  HopfAlgebra.canMap_surjective_of_surjective _ Function.surjective_id _

/-- Left integrals on `ℚ[C₃]`: the family is nonempty, every left integral vanishes at `g`
(`Λ g • g = Λ g • 1` from `Δ g = g ⊗ g`), and `∑ j, Λ j (u j) = ε 1 = 1`. -/
example : ∃ (n : ℕ) (Λ : Fin n → Module.Dual ℚ QC₃) (u : Fin n → QC₃),
    0 < n ∧ (∀ j, Λ j g = 0) ∧ ∑ j, Λ j (u j) = 1 := by
  obtain ⟨n, Λ, u, hΛ, h⟩ :=
    HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit (R := ℚ) (B := QC₃)
  have h1 : ∑ j, Λ j (u j) = 1 := by simpa using h 1
  refine ⟨n, Λ, u, Nat.pos_of_ne_zero fun hn => ?_, fun j => ?_, h1⟩
  · subst hn
    simp at h1
  · have hj := hΛ j g
    rw [(isGroupLikeElem_single_one gen).comul_eq_tmul_self, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul] at hj
    by_contra hne
    exact g_ne_one (smul_right_injective QC₃ hne hj)

end HopfOrderTest
