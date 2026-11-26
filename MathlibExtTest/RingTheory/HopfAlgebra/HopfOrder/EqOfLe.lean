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
    HopfOrder.tensorSqHom S (Coalgebra.comul (R := ℤ) gS) = g ⊗ₜ[ℚ] g := by
  change HopfOrder.tensorSqHom S (HopfOrder.comulS hcomul gS) = g ⊗ₜ[ℚ] g
  exact (HopfOrder.exists_tensorSqHom_eq_comul hcomul gS).choose_spec.trans
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

/-! ### Two nested Hopf orders in `ℚ[C₂]` and the counit quotient -/

namespace HopfOrderQuotientTest

open MonoidAlgebra

/-- The cyclic group of order two, written multiplicatively. -/
private abbrev C₂ : Type := Multiplicative (ZMod 2)

/-- The group algebra `ℚ[C₂]`. -/
private abbrev QC₂ : Type := MonoidAlgebra ℚ C₂

/-- The nonidentity element of `C₂`. -/
private abbrev σ₂ : C₂ := Multiplicative.ofAdd 1

/-- The basis element of `ℚ[C₂]` at `σ₂`. -/
private noncomputable abbrev u : QC₂ := single σ₂ 1

/-- The element `e = (u - 1) / 2` of `ℚ[C₂]`. -/
private noncomputable abbrev e : QC₂ := (2 : ℚ)⁻¹ • (u - 1)

/-- The group ring `ℤ[C₂]`, generated by `u`. -/
private noncomputable abbrev T₀ : Subalgebra ℤ QC₂ := Algebra.adjoin ℤ {u}

/-- The Hopf order generated by `e`, which strictly contains `ℤ[C₂]`. -/
private noncomputable abbrev T₁ : Subalgebra ℤ QC₂ := Algebra.adjoin ℤ {e}

/-- The counit `ℚ[C₂] → ℚ`, a surjective bialgebra map that is not the identity. -/
private noncomputable abbrev ε₂ : QC₂ →ₐc[ℚ] ℚ := Bialgebra.counitBialgHom ℚ QC₂

private theorem u_mul_u : u * u = 1 := by
  rw [single_mul_single, mul_one, one_def]
  rfl

private theorem e_mul_e : e * e = -e := by
  simp only [e, smul_mul_smul_comm, sub_mul, mul_sub, u_mul_u, one_mul, mul_one]
  module

private theorem u_mem_T₁ : u ∈ T₁ := by
  have h : u = 1 + 2 • e := by simp only [e]; module
  rw [h]
  exact add_mem (one_mem _) (nsmul_mem (Algebra.subset_adjoin rfl) 2)

private theorem T₀_le_T₁ : T₀ ≤ T₁ := Algebra.adjoin_le (Set.singleton_subset_iff.mpr u_mem_T₁)

/-- `T₀ = ℤ[C₂]` lies in the `ℤ`-span of `1` and `u`, since `u * u = 1`. -/
private theorem mem_span_of_mem_T₀ {x : QC₂} (hx : x ∈ T₀) :
    x ∈ Submodule.span ℤ {(1 : QC₂), u} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact Submodule.subset_span (by simp)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span (by simp))
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
    refine Submodule.mem_span_pair.mpr ⟨a * c + b * d, a * d + b * c, ?_⟩
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, u_mul_u]
    module

/-- `e = (u - 1) / 2` is not in `ℤ[C₂]`: its coefficient at `1` is `-1/2`. -/
private theorem e_not_mem_T₀ : e ∉ T₀ := fun h => by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (mem_span_of_mem_T₀ h)
  have h1 :=
    congrArg (Finsupp.lapply (1 : C₂) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) hab
  have hσ : σ₂ ≠ 1 := by decide
  simp [e, one_def, hσ] at h1
  have h2 : (2 * a : ℚ) = -1 := by rw [h1]; norm_num
  have h3 : 2 * a = -1 := by exact_mod_cast h2
  omega

private theorem T₀_ne_T₁ : T₀ ≠ T₁ := fun h => e_not_mem_T₀ (h ▸ Algebra.subset_adjoin rfl)

private theorem hcounit₀ : ∀ x ∈ T₀, Coalgebra.counit (R := ℚ) x ∈ (algebraMap ℤ ℚ).range := by
  intro x hx
  have h : T₀.map ((Bialgebra.counitAlgHom ℚ QC₂).restrictScalars ℤ) ≤ ⊥ := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    simp
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩))
  exact ⟨r, hr⟩

private theorem hcounit₁ : ∀ x ∈ T₁, Coalgebra.counit (R := ℚ) x ∈ (algebraMap ℤ ℚ).range := by
  intro x hx
  have h : T₁.map ((Bialgebra.counitAlgHom ℚ QC₂).restrictScalars ℤ) ≤ ⊥ := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    simp [e]
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩))
  exact ⟨r, hr⟩

private theorem hcomul₀ : ∀ x ∈ T₀, Coalgebra.comul (R := ℚ) x ∈
    (Algebra.TensorProduct.productMap
      (((Algebra.TensorProduct.includeLeft : QC₂ →ₐ[ℚ] QC₂ ⊗[ℚ] QC₂).restrictScalars ℤ).comp T₀.val)
      (((Algebra.TensorProduct.includeRight : QC₂ →ₐ[ℚ] QC₂ ⊗[ℚ] QC₂).restrictScalars ℤ).comp
        T₀.val)).range := by
  intro x hx
  have h : T₀.map ((Bialgebra.comulAlgHom ℚ QC₂).restrictScalars ℤ) ≤
      (HopfOrder.tensorSqHom (K := ℚ) T₀).range := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    rw [AlgHom.restrictScalars_apply, Bialgebra.comulAlgHom_apply,
      (isGroupLikeElem_single_one σ₂).comul_eq_tmul_self]
    exact HopfOrder.tmul_mem_range_tensorSqHom (Algebra.subset_adjoin rfl)
      (Algebra.subset_adjoin rfl)
  exact h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)

/-- `Δ e = e ⊗ 1 + 1 ⊗ e + 2 • (e ⊗ e)`, so the comultiplication preserves `T₁`. -/
private theorem comul_e : Coalgebra.comul (R := ℚ) e =
    e ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] e + 2 • (e ⊗ₜ[ℚ] e) := by
  rw [map_smul, map_sub, (isGroupLikeElem_single_one σ₂).comul_eq_tmul_self, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def]
  simp only [e, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub]
  module

private theorem hcomul₁ : ∀ x ∈ T₁, Coalgebra.comul (R := ℚ) x ∈
    (Algebra.TensorProduct.productMap
      (((Algebra.TensorProduct.includeLeft : QC₂ →ₐ[ℚ] QC₂ ⊗[ℚ] QC₂).restrictScalars ℤ).comp T₁.val)
      (((Algebra.TensorProduct.includeRight : QC₂ →ₐ[ℚ] QC₂ ⊗[ℚ] QC₂).restrictScalars ℤ).comp
        T₁.val)).range := by
  intro x hx
  have he : e ∈ T₁ := Algebra.subset_adjoin rfl
  have h : T₁.map ((Bialgebra.comulAlgHom ℚ QC₂).restrictScalars ℤ) ≤
      (HopfOrder.tensorSqHom (K := ℚ) T₁).range := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    rw [AlgHom.restrictScalars_apply, Bialgebra.comulAlgHom_apply, comul_e]
    exact add_mem (add_mem (HopfOrder.tmul_mem_range_tensorSqHom he (one_mem _))
      (HopfOrder.tmul_mem_range_tensorSqHom (one_mem _) he))
      (nsmul_mem (HopfOrder.tmul_mem_range_tensorSqHom he he) 2)
  exact h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem hantipode₀ : ∀ x ∈ T₀, HopfAlgebra.antipode ℚ (A := QC₂) x ∈ T₀ := by
  intro x hx
  have h : T₀.map ((HopfAlgebra.antipodeAlgHom ℚ QC₂).restrictScalars ℤ) ≤ T₀ := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    change HopfAlgebra.antipode ℚ u ∈ T₀
    rw [antipode_single, HopfAlgebra.antipode_one]
    exact Algebra.subset_adjoin rfl
  exact h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem hantipode₁ : ∀ x ∈ T₁, HopfAlgebra.antipode ℚ (A := QC₂) x ∈ T₁ := by
  intro x hx
  have h : T₁.map ((HopfAlgebra.antipodeAlgHom ℚ QC₂).restrictScalars ℤ) ≤ T₁ := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    change HopfAlgebra.antipode ℚ e ∈ T₁
    rw [map_smul, map_sub, antipode_single, HopfAlgebra.antipode_one, HopfAlgebra.antipode_one]
    exact Algebra.subset_adjoin rfl
  exact h (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)

private instance hfin₀ : Module.Finite ℤ T₀ :=
  Algebra.finite_adjoin_simple_of_isIntegral
    (IsIntegral.of_pow two_pos (by rw [sq, u_mul_u]; exact isIntegral_one))

/-- `e` is integral over `ℤ`, a root of `X ^ 2 + X`. -/
private instance hfin₁ : Module.Finite ℤ T₁ := by
  refine Algebra.finite_adjoin_simple_of_isIntegral ⟨Polynomial.X ^ 2 + Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_add (by rw [Polynomial.degree_X]; norm_num)
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, sq, e_mul_e,
      neg_add_cancel]

private theorem hspan₀ : Submodule.span ℚ (T₀ : Set QC₂) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of h =>
    have : h = 1 ∨ h = σ₂ := by revert h; decide
    rcases this with rfl | rfl
    · exact Submodule.subset_span (show of ℚ C₂ 1 ∈ T₀ from one_mem _)
    · exact Submodule.subset_span (show of ℚ C₂ σ₂ ∈ T₀ from Algebra.subset_adjoin rfl)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul r x hx => exact Submodule.smul_mem _ r hx

private theorem hspan₁ : Submodule.span ℚ (T₁ : Set QC₂) = ⊤ :=
  top_le_iff.mp (hspan₀ ▸ Submodule.span_mono (SetLike.coe_subset_coe.mpr T₀_le_T₁))

private theorem counit_surjective₂ : Function.Surjective ε₂ :=
  fun r => ⟨algebraMap ℚ QC₂ r, by simp⟩

/-- Every element is coinvariant for the counit: `(id ⊗ ε) (Δ a) = a ⊗ 1`. -/
private theorem mem_hopfKer_ε₂ (a : QC₂) : a ∈ HopfAlgebra.hopfKer ε₂ := by
  rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply, ← Coalgebra.lTensor_counit_comul a]
  induction Coalgebra.comul (R := ℚ) a using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The image comparison for the counit quotient: `ℤ[C₂]` and `T₁` both map onto `ℤ`. -/
private theorem himg₂ : T₀.map ((ε₂ : QC₂ →ₐ[ℚ] ℚ).restrictScalars ℤ) =
    T₁.map ((ε₂ : QC₂ →ₐ[ℚ] ℚ).restrictScalars ℤ) := by
  have key : ∀ T : Subalgebra ℤ QC₂,
      (∀ x ∈ T, Coalgebra.counit (R := ℚ) x ∈ (algebraMap ℤ ℚ).range) →
      T.map ((ε₂ : QC₂ →ₐ[ℚ] ℚ).restrictScalars ℤ) = ⊥ := by
    intro T hT
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    obtain ⟨r, hr⟩ := hT x hx
    exact Algebra.mem_bot.mpr ⟨r, hr⟩
  rw [key T₀ hcounit₀, key T₁ hcounit₁]

/-- The kernel comparison for the counit quotient fails: the Hopf kernel of the counit is all of
`ℚ[C₂]`, and `e` lies in `T₁` but not in `ℤ[C₂]`. -/
example : T₀.comap (((HopfAlgebra.hopfKer ε₂).val : _ →ₐ[ℚ] QC₂).restrictScalars ℤ) ≠
    T₁.comap (((HopfAlgebra.hopfKer ε₂).val : _ →ₐ[ℚ] QC₂).restrictScalars ℤ) := by
  intro h
  have h1 : (⟨e, mem_hopfKer_ε₂ e⟩ : HopfAlgebra.hopfKer ε₂) ∈
      T₁.comap (((HopfAlgebra.hopfKer ε₂).val : _ →ₐ[ℚ] QC₂).restrictScalars ℤ) :=
    Algebra.subset_adjoin rfl
  rw [← h] at h1
  exact e_not_mem_T₀ h1

/-- The main theorem with the counit quotient: `ℤ[C₂] ≤ T₁` are distinct Hopf orders spanning
`ℚ[C₂]` with the same image under the counit, so their intersections with its Hopf kernel
differ. -/
example : T₀.comap (((HopfAlgebra.hopfKer ε₂).val : _ →ₐ[ℚ] QC₂).restrictScalars ℤ) ≠
    T₁.comap (((HopfAlgebra.hopfKer ε₂).val : _ →ₐ[ℚ] QC₂).restrictScalars ℤ) := fun hker =>
  T₀_ne_T₁ (HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq T₀_le_T₁ hfin₀ hspan₀ hcomul₀
    hantipode₀ hcounit₀ hfin₁ hspan₁ hcomul₁ hantipode₁ hcounit₁ ε₂ counit_surjective₂ hker himg₂)

end HopfOrderQuotientTest
