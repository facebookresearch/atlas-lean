/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DrinfeldDatum_Iso_subsingleton`
`CF_DrinfeldDatum_BaseChangeAlong_exists_comp`
`CF_DrinfeldDatum_BaseChangeAlong_exists_iso`
`CF_DrinfeldDatum_BaseChangeAlong_tau_unique`
`CF_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization`
`CF_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic`
`CF_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong`
`CF_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleBaseChangeAux

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.DrinfeldDatum

/-- Two isomorphisms of Drinfeld data agree: the module isomorphisms are determined by their
effect on the stalk maps `u₀`, `u₁`, which are surjective. -/
theorem Iso.subsingleton
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q Q' : DrinfeldDatum (K := K) π B) : Subsingleton (Q.Iso Q') := by
  classical
  refine ⟨fun I I' => ?_⟩
  have h0 : I.τ₀ = I'.τ₀ := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro t
    apply Module.eq_of_localization_maximal
      (fun (P : Ideal B) _ => LocalizedModule P.primeCompl Q'.T₀)
      (fun (P : Ideal B) _ => LocalizedModule.mkLinearMap P.primeCompl Q'.T₀)
    intro P hP
    let x : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    have key : ∀ w : stalk B x Q.T₀,
        LocalizedModule.map x.asIdeal.primeCompl I.τ₀.toLinearMap w =
          LocalizedModule.map x.asIdeal.primeCompl I'.τ₀.toLinearMap w := by
      intro w
      obtain ⟨z, rfl⟩ := Q.u₀_surjective x w
      induction z using TensorProduct.inductionOn with
      | tmul b v =>
        have hv' : (v : Fin 2 → K) ∈ Q'.N₀ x := by rw [← I.N₀_eq]; exact v.2
        have e : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e, map_smul, map_smul, map_smul]
        have h1 := I.τ₀_u₀ x v v.2 hv'
        have h2 := I'.τ₀_u₀ x v v.2 hv'
        rw [Subtype.coe_eta] at h1 h2
        rw [← h1, ← h2]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    have := key (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q.T₀ t)
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, LocalizedModule.map_mk] at this
    exact this
  have h1 : I.τ₁ = I'.τ₁ := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro t
    apply Module.eq_of_localization_maximal
      (fun (P : Ideal B) _ => LocalizedModule P.primeCompl Q'.T₁)
      (fun (P : Ideal B) _ => LocalizedModule.mkLinearMap P.primeCompl Q'.T₁)
    intro P hP
    let x : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    have key : ∀ w : stalk B x Q.T₁,
        LocalizedModule.map x.asIdeal.primeCompl I.τ₁.toLinearMap w =
          LocalizedModule.map x.asIdeal.primeCompl I'.τ₁.toLinearMap w := by
      intro w
      obtain ⟨z, rfl⟩ := Q.u₁_surjective x w
      induction z using TensorProduct.inductionOn with
      | tmul b v =>
        have hv' : (v : Fin 2 → K) ∈ Q'.N₁ x := by rw [← I.N₁_eq]; exact v.2
        have e : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e, map_smul, map_smul, map_smul]
        have h1 := I.τ₁_u₁ x v v.2 hv'
        have h2 := I'.τ₁_u₁ x v v.2 hv'
        rw [Subtype.coe_eta] at h1 h2
        rw [← h1, ← h2]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    have := key (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q.T₁ t)
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, LocalizedModule.map_mk] at this
    exact this
  cases I; cases I'
  simp only at h0 h1
  subst h0; subst h1
  rfl

/-- Composite of two semilinear maps along `g` and then `h`, semilinear along `h.comp g`. -/
private def bcComp {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] {B'' : Type} [CommRing B''] [Algebra 𝒪 B'']
    (g : B →ₐ[𝒪] B') (h : B' →ₐ[𝒪] B'')
    {M : Type} [AddCommGroup M] [Module B M] {M' : Type} [AddCommGroup M'] [Module B' M']
    {M'' : Type} [AddCommGroup M''] [Module B'' M'']
    (τ : M →ₛₗ[(g : B →+* B')] M') (τ' : M' →ₛₗ[(h : B' →+* B'')] M'') :
    M →ₛₗ[((h.comp g) : B →+* B'')] M'' where
  toFun t := τ' (τ t)
  map_add' a b := by simp
  map_smul' b t := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    rfl

private theorem bcComp_apply {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] {B'' : Type} [CommRing B''] [Algebra 𝒪 B'']
    (g : B →ₐ[𝒪] B') (h : B' →ₐ[𝒪] B'')
    {M : Type} [AddCommGroup M] [Module B M] {M' : Type} [AddCommGroup M'] [Module B' M']
    {M'' : Type} [AddCommGroup M''] [Module B'' M'']
    (τ : M →ₛₗ[(g : B →+* B')] M') (τ' : M' →ₛₗ[(h : B' →+* B'')] M'') (t : M) :
    bcComp g h τ τ' t = τ' (τ t) := rfl

private theorem span_range_bcComp {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] {B'' : Type} [CommRing B'']
    [Algebra 𝒪 B''] (g : B →ₐ[𝒪] B') (h : B' →ₐ[𝒪] B'')
    {M : Type} [AddCommGroup M] [Module B M] {M' : Type} [AddCommGroup M'] [Module B' M']
    {M'' : Type} [AddCommGroup M''] [Module B'' M'']
    (τ : M →ₛₗ[(g : B →+* B')] M') (τ' : M' →ₛₗ[(h : B' →+* B'')] M'')
    (h1 : Submodule.span B' (Set.range τ) = ⊤) (h2 : Submodule.span B'' (Set.range τ') = ⊤) :
    Submodule.span B'' (Set.range (bcComp g h τ τ')) = ⊤ := by
  apply top_le_iff.mp
  rw [← h2]
  apply Submodule.span_le.mpr
  rintro _ ⟨t', rfl⟩
  have ht' : t' ∈ Submodule.span B' (Set.range τ) := by rw [h1]; trivial
  induction ht' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨t, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- Base changes compose: a base change along `g` followed by one along `h` gives a base change
along `h.comp g` whose module maps are the composites. -/
theorem BaseChangeAlong.exists_comp
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {B'' : Type} [CommRing B''] [Algebra 𝒪 B''] (g : B →ₐ[𝒪] B') (h : B' →ₐ[𝒪] B'')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'}
    {Q'' : DrinfeldDatum (K := K) π B''}
    (W : Q.BaseChangeAlong g Q') (W' : Q'.BaseChangeAlong h Q'') :
    ∃ W'' : Q.BaseChangeAlong (h.comp g) Q'',
      (∀ t, W''.τ₀ t = W'.τ₀ (W.τ₀ t)) ∧ (∀ t, W''.τ₁ t = W'.τ₁ (W.τ₁ t)) := by
  refine ⟨{ N₀_eq := ?_, N₁_eq := ?_, τ₀ := bcComp g h W.τ₀ W'.τ₀, τ₁ := bcComp g h W.τ₁ W'.τ₁,
            span_range_τ₀ := span_range_bcComp g h _ _ W.span_range_τ₀ W'.span_range_τ₀,
            span_range_τ₁ := span_range_bcComp g h _ _ W.span_range_τ₁ W'.span_range_τ₁,
            τ₁_Pi₀ := ?_, τ₀_Pi₁ := ?_, u₀_eq := ?_, u₁_eq := ?_ }, fun _ => rfl, fun _ => rfl⟩
  · intro x''; rw [W'.N₀_eq, W.N₀_eq]; rfl
  · intro x''; rw [W'.N₁_eq, W.N₁_eq]; rfl
  · intro t; simp only [bcComp_apply, W.τ₁_Pi₀, W'.τ₁_Pi₀]
  · intro t; simp only [bcComp_apply, W.τ₀_Pi₁, W'.τ₀_Pi₁]
  · intro x'' v hv hv'' t s hs H
    have hv' : v ∈ Q'.N₀ (pointUnder h x'') := by rw [W.N₀_eq]; exact hv
    have h1 := W.u₀_eq (pointUnder h x'') v hv hv' t s hs H
    exact W'.u₀_eq x'' v hv' hv'' (W.τ₀ t) (g s) hs h1
  · intro x'' v hv hv'' t s hs H
    have hv' : v ∈ Q'.N₁ (pointUnder h x'') := by rw [W.N₁_eq]; exact hv
    have h1 := W.u₁_eq (pointUnder h x'') v hv hv' t s hs H
    exact W'.u₁_eq x'' v hv' hv'' (W.τ₁ t) (g s) hs h1

/-- Two spanning semilinear maps from an invertible module into invertible modules differ by a
unique linear equivalence. -/
private theorem bcIso_exists_equiv {B : Type} [CommRing B] {B' : Type} [CommRing B']
    (φ : B →+* B')
    (T : Type) [AddCommGroup T] [Module B T]
    (T' : Type) [AddCommGroup T'] [Module B' T'] [Module.Invertible B' T']
    (T'' : Type) [AddCommGroup T''] [Module B' T''] [Module.Invertible B' T'']
    (τ' : T →ₛₗ[φ] T') (τ'' : T →ₛₗ[φ] T'')
    (h' : Submodule.span B' (Set.range τ') = ⊤) (h'' : Submodule.span B' (Set.range τ'') = ⊤)
    [Module.Invertible B T] :
    ∃ e : T' ≃ₗ[B'] T'', ∀ t, e (τ' t) = τ'' t := by
  let _ : Algebra B B' := φ.toAlgebra
  let _ : Module B T' := Module.compHom T' φ
  let _ : Module B T'' := Module.compHom T'' φ
  have _ : IsScalarTower B B' T' := ⟨fun b c t => by
    change (b • c) • t = (φ b) • (c • t); rw [Algebra.smul_def, mul_smul]; rfl⟩
  have _ : IsScalarTower B B' T'' := ⟨fun b c t => by
    change (b • c) • t = (φ b) • (c • t); rw [Algebra.smul_def, mul_smul]; rfl⟩
  let σ' : T →ₗ[B] T' :=
    { toFun := τ'
      map_add' := fun a b => map_add τ' a b
      map_smul' := fun b t => by rw [LinearMap.map_smulₛₗ]; rfl }
  let σ'' : T →ₗ[B] T'' :=
    { toFun := τ''
      map_add' := fun a b => map_add τ'' a b
      map_smul' := fun b t => by rw [LinearMap.map_smulₛₗ]; rfl }
  have hs' : Function.Surjective (σ'.liftBaseChange B') := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← h']
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  have hs'' : Function.Surjective (σ''.liftBaseChange B') := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← h'']
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  let e' := LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hs')
  let e'' := LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hs'')
  refine ⟨e'.symm.trans e'', fun t => ?_⟩
  have h1 : e' ((1 : B') ⊗ₜ[B] t) = τ' t := by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  have h2 : e'' ((1 : B') ⊗ₜ[B] t) = τ'' t := by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  rw [LinearEquiv.trans_apply, ← h1, LinearEquiv.symm_apply_apply, h2]

private theorem bcIso_exists_mk {B : Type} [CommRing B] (S : Submonoid B) {M : Type}
    [AddCommGroup M] [Module B M] (m : LocalizedModule S M) :
    ∃ (t : M) (s : S), m = LocalizedModule.mk t s := by
  induction m using LocalizedModule.induction_on with
  | h t s => exact ⟨t, s, rfl⟩

/-- Two base changes of the same datum along the same map are isomorphic, compatibly with the
module maps. -/
theorem BaseChangeAlong.exists_iso
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (g : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (W : Q.BaseChangeAlong g Q') (W' : Q.BaseChangeAlong g Q'') :
    ∃ e : Q'.Iso Q'', (∀ t, e.τ₀ (W.τ₀ t) = W'.τ₀ t) ∧ (∀ t, e.τ₁ (W.τ₁ t) = W'.τ₁ t) := by
  obtain ⟨e₀, he₀⟩ := bcIso_exists_equiv (g : B →+* B') Q.T₀ Q'.T₀ Q''.T₀ W.τ₀ W'.τ₀
    W.span_range_τ₀ W'.span_range_τ₀
  obtain ⟨e₁, he₁⟩ := bcIso_exists_equiv (g : B →+* B') Q.T₁ Q'.T₁ Q''.T₁ W.τ₁ W'.τ₁
    W.span_range_τ₁ W'.span_range_τ₁
  refine ⟨{ N₀_eq := fun x' => by rw [W.N₀_eq, W'.N₀_eq],
            N₁_eq := fun x' => by rw [W.N₁_eq, W'.N₁_eq],
            τ₀ := e₀, τ₁ := e₁, τ₁_Pi₀ := ?_, τ₀_Pi₁ := ?_, τ₀_u₀ := ?_, τ₁_u₁ := ?_ }, he₀, he₁⟩
  · have key : e₁.toLinearMap ∘ₗ Q'.Pi₀ = Q''.Pi₀ ∘ₗ e₀.toLinearMap := by
      apply LinearMap.ext_on W.span_range_τ₀
      rintro _ ⟨t, rfl⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [← W.τ₁_Pi₀, he₁, W'.τ₁_Pi₀, he₀]
    intro t
    exact congrArg (fun f => f t) (congrArg DFunLike.coe key)
  · have key : e₀.toLinearMap ∘ₗ Q'.Pi₁ = Q''.Pi₁ ∘ₗ e₁.toLinearMap := by
      apply LinearMap.ext_on W.span_range_τ₁
      rintro _ ⟨t, rfl⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [← W.τ₀_Pi₁, he₀, W'.τ₀_Pi₁, he₁]
    intro t
    exact congrArg (fun f => f t) (congrArg DFunLike.coe key)
  · intro x' v hv hv'
    have hvQ : v ∈ Q.N₀ (pointUnder g x') := by rw [← W.N₀_eq]; exact hv
    obtain ⟨t, s, H⟩ := bcIso_exists_mk _ (Q.u₀ (pointUnder g x')
      ((1 : locRing B (pointUnder g x')) ⊗ₜ[𝒪] (⟨v, hvQ⟩ : ↥(Q.N₀ (pointUnder g x')))))
    have h1 := W.u₀_eq x' v hvQ hv t s s.2 H
    have h2 := W'.u₀_eq x' v hvQ hv' t s s.2 H
    rw [h1, h2, LocalizedModule.map_mk]
    exact congrArg (fun m => LocalizedModule.mk m _) (he₀ t).symm
  · intro x' v hv hv'
    have hvQ : v ∈ Q.N₁ (pointUnder g x') := by rw [← W.N₁_eq]; exact hv
    obtain ⟨t, s, H⟩ := bcIso_exists_mk _ (Q.u₁ (pointUnder g x')
      ((1 : locRing B (pointUnder g x')) ⊗ₜ[𝒪] (⟨v, hvQ⟩ : ↥(Q.N₁ (pointUnder g x')))))
    have h1 := W.u₁_eq x' v hvQ hv t s s.2 H
    have h2 := W'.u₁_eq x' v hvQ hv' t s s.2 H
    rw [h1, h2, LocalizedModule.map_mk]
    exact congrArg (fun m => LocalizedModule.mk m _) (he₁ t).symm

/-- The identity isomorphism of a Drinfeld datum. -/
private def bcIsoRefl {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (Q : DrinfeldDatum (K := K) π B) : Q.Iso Q where
  N₀_eq _ := rfl
  N₁_eq _ := rfl
  τ₀ := LinearEquiv.refl B Q.T₀
  τ₁ := LinearEquiv.refl B Q.T₁
  τ₁_Pi₀ _ := rfl
  τ₀_Pi₁ _ := rfl
  τ₀_u₀ x v hv hv' := by
    rw [LinearEquiv.refl_toLinearMap, LocalizedModule.map_id]; rfl
  τ₁_u₁ x v hv hv' := by
    rw [LinearEquiv.refl_toLinearMap, LocalizedModule.map_id]; rfl

/-- The module maps of a base change along `g` from `Q` to `Q'` are unique. -/
theorem BaseChangeAlong.tau_unique
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (g : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'}
    (W W' : Q.BaseChangeAlong g Q') :
    (∀ t, W.τ₀ t = W'.τ₀ t) ∧ (∀ t, W.τ₁ t = W'.τ₁ t) := by
  obtain ⟨e, he₀, he₁⟩ := BaseChangeAlong.exists_iso g W W'
  have hsub := Iso.subsingleton Q' Q'
  have he : e = bcIsoRefl Q' := hsub.elim e _
  subst he
  exact ⟨fun t => (he₀ t).symm.trans rfl |>.symm, fun t => (he₁ t).symm.trans rfl |>.symm⟩

private theorem bcIsIso_map_mk {R : Type} [CommRing R] (S : Submonoid R) {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (m : M)
    (s : S) :
    LocalizedModule.map S g (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s :=
  LocalizedModule.map_mk S g m s

private theorem bcIsIso_span_comp {R : Type} [CommRing R] {σ : Type} {N P : Type}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (τ : σ → N) (e : N ≃ₗ[R] P) (h : Submodule.span R (Set.range τ) = ⊤) :
    Submodule.span R (Set.range fun t => e (τ t)) = ⊤ := by
  have : (Set.range fun t => e (τ t)) = e '' Set.range τ := by
    ext p; simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
  rw [this, show (⇑e '' Set.range τ) = e.toLinearMap '' Set.range τ from rfl,
    Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

/-- Being a base change along `f` is invariant under isomorphism of the target datum. -/
theorem isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (h : Q.IsBaseChangeAlong f Q') (e : Q'.IsIsomorphic Q'') : Q.IsBaseChangeAlong f Q'' := by
  obtain ⟨W⟩ := h
  obtain ⟨E⟩ := e
  refine ⟨{
    N₀_eq := fun x' => (E.N₀_eq x').symm.trans (W.N₀_eq x')
    N₁_eq := fun x' => (E.N₁_eq x').symm.trans (W.N₁_eq x')
    τ₀ := E.τ₀.toLinearMap.comp W.τ₀
    τ₁ := E.τ₁.toLinearMap.comp W.τ₁
    span_range_τ₀ := ?_
    span_range_τ₁ := ?_
    τ₁_Pi₀ := fun t => ?_
    τ₀_Pi₁ := fun t => ?_
    u₀_eq := ?_
    u₁_eq := ?_ }⟩
  · exact bcIsIso_span_comp W.τ₀ E.τ₀ W.span_range_τ₀
  · exact bcIsIso_span_comp W.τ₁ E.τ₁ W.span_range_τ₁
  · change E.τ₁ (W.τ₁ (Q.Pi₀ t)) = Q''.Pi₀ (E.τ₀ (W.τ₀ t))
    rw [W.τ₁_Pi₀, E.τ₁_Pi₀]
  · change E.τ₀ (W.τ₀ (Q.Pi₁ t)) = Q''.Pi₁ (E.τ₁ (W.τ₁ t))
    rw [W.τ₀_Pi₁, E.τ₀_Pi₁]
  · intro x' v hv hv'' t s hs H
    have hv' : v ∈ Q'.N₀ x' := by rw [E.N₀_eq]; exact hv''
    rw [E.τ₀_u₀ x' v hv' hv'', W.u₀_eq x' v hv hv' t s hs H]
    exact bcIsIso_map_mk _ _ _ _
  · intro x' v hv hv'' t s hs H
    have hv' : v ∈ Q'.N₁ x' := by rw [E.N₁_eq]; exact hv''
    rw [E.τ₁_u₁ x' v hv' hv'', W.u₁_eq x' v hv hv' t s hs H]
    exact bcIsIso_map_mk _ _ _ _

/-- The base change of a Drinfeld datum to a localization exists. -/
theorem exists_isBaseChangeAlong_of_isLocalization
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (Q : DrinfeldDatum (K := K) π B) (S : Submonoid B)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
    [IsLocalization S C] :
    ∃ Q' : DrinfeldDatum (K := K) π C, Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B C) Q' :=
  ⟨LocBC.bcDatum S Q, LocBC.isBaseChangeAlong_bcDatum S Q⟩

namespace QuadNat

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

section LocMap

variable (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')

/-- The local homomorphism of local rings induced by `f` at `x'`. -/
private def locMap : locRing B (pointUnder f x') →ₐ[𝒪] locRing B' x' :=
  Localization.localAlgHom (pointUnder f x').asIdeal x'.asIdeal f rfl

private theorem locMap_algebraMap (b : B) :
    locMap f x' (algebraMap B (locRing B (pointUnder f x')) b) =
      algebraMap B' (locRing B' x') (f b) :=
  Localization.localRingHom_to_map _ _ _ rfl b

private theorem toLocRing_comp :
    (toLocRing B' x').comp f = (locMap f x').comp (toLocRing B (pointUnder f x')) := by
  apply AlgHom.ext
  intro b
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change algebraMap B' (locRing B' x') (f b) =
    locMap f x' (algebraMap B (locRing B (pointUnder f x')) b)
  rw [locMap_algebraMap]

private theorem locMap_mk (b : B) (s : (pointUnder f x').asIdeal.primeCompl) :
    locMap f x' (Localization.mk b s) =
      Localization.mk (f b) (⟨f s, s.2⟩ : x'.asIdeal.primeCompl) := by
  change Localization.localRingHom (pointUnder f x').asIdeal x'.asIdeal f.toRingHom rfl
    (Localization.mk b s) = _
  rw [Localization.mk_eq_mk']
  erw [Localization.localRingHom_mk']
  rw [Localization.mk_eq_mk']
  rfl

end LocMap

section StalkMap

variable (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')
variable {T : Type} [AddCommGroup T] [Module B T] {T' : Type} [AddCommGroup T'] [Module B' T']
variable (τ : T →ₛₗ[(f : B →+* B')] T')

private theorem τ_smul (b : B) (t : T) : τ (b • t) = f b • τ t := LinearMap.map_smulₛₗ τ b t

private theorem stalkMap_wd (p p' : T × (pointUnder f x').asIdeal.primeCompl) (h : p ≈ p') :
    (LocalizedModule.mk (τ p.1) (⟨f p.2, p.2.2⟩ : x'.asIdeal.primeCompl) : stalk B' x' T') =
      LocalizedModule.mk (τ p'.1) (⟨f p'.2, p'.2.2⟩ : x'.asIdeal.primeCompl) := by
  obtain ⟨u, hu⟩ := h
  rw [LocalizedModule.mk_eq]
  refine ⟨⟨f u, u.2⟩, ?_⟩
  have hu' := congrArg τ hu
  simp only [Submonoid.smul_def, τ_smul] at hu'
  simp only [Submonoid.smul_def]
  exact hu'

/-- The map of stalks induced by a semilinear map `τ` along `f`. -/
private def stalkMap (m : stalk B (pointUnder f x') T) : stalk B' x' T' :=
  m.liftOn (fun p => LocalizedModule.mk (τ p.1) (⟨f p.2, p.2.2⟩ : x'.asIdeal.primeCompl))
    (stalkMap_wd f x' τ)

private theorem stalkMap_mk (t : T) (s : (pointUnder f x').asIdeal.primeCompl) :
    stalkMap f x' τ (LocalizedModule.mk t s) =
      LocalizedModule.mk (τ t) (⟨f s, s.2⟩ : x'.asIdeal.primeCompl) :=
  LocalizedModule.liftOn_mk _ t s

private theorem stalkMap_zero : stalkMap f x' τ 0 = 0 := by
  rw [← LocalizedModule.zero_mk 1, stalkMap_mk, map_zero, LocalizedModule.zero_mk]

private theorem stalkMap_add (m m' : stalk B (pointUnder f x') T) :
    stalkMap f x' τ (m + m') = stalkMap f x' τ m + stalkMap f x' τ m' := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    induction m' using LocalizedModule.induction_on with
    | h t' s' =>
      rw [LocalizedModule.mk_add_mk, stalkMap_mk, stalkMap_mk, stalkMap_mk,
        LocalizedModule.mk_add_mk, map_add]
      simp only [Submonoid.smul_def, τ_smul]
      congr 1
      exact Subtype.ext (by simp only [Submonoid.coe_mul, map_mul])

private theorem stalkMap_smul (r : locRing B (pointUnder f x')) (m : stalk B (pointUnder f x') T) :
    stalkMap f x' τ (r • m) = locMap f x' r • stalkMap f x' τ m := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    induction r using Localization.induction_on with
    | H y =>
      obtain ⟨b, s'⟩ := y
      rw [LocalizedModule.mk_smul_mk, stalkMap_mk, stalkMap_mk, locMap_mk,
        LocalizedModule.mk_smul_mk, τ_smul]
      congr 1
      exact Subtype.ext (by simp only [Submonoid.coe_mul, map_mul])

private theorem exists_mk {C : Type} [CommRing C] {S : Submonoid C} {M : Type} [AddCommGroup M]
    [Module C M] (m : LocalizedModule S M) : ∃ (t : M) (s : S), LocalizedModule.mk t s = m := by
  induction m using LocalizedModule.induction_on with
  | h t s => exact ⟨t, s, rfl⟩

end StalkMap

section Kernel

variable (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')

private theorem map_map_toLocRing (d : DeligneDatum (K := K) π B) :
    (d.map π f).map π (toLocRing B' x') =
      (d.map π (toLocRing B (pointUnder f x'))).map π (locMap f x') := by
  rw [← DeligneDatum.map_comp, ← DeligneDatum.map_comp, toLocRing_comp]

variable {N N' : Submodule 𝒪 (Fin 2 → K)} (hN : Submodule.IsFullLattice K N)
  (hN' : Submodule.IsFullLattice K N')
variable {T : Type} [AddCommGroup T] [Module B T] {T' : Type} [AddCommGroup T'] [Module B' T']
variable [Module.Invertible B T] [Module.Invertible B' T']
variable (τ : T →ₛₗ[(f : B →+* B')] T')
variable (u : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩
  →ₗ[locRing B (pointUnder f x')] stalk B (pointUnder f x') T)
variable (u' : latticeBaseChange 𝒪 K (locRing B' x') ⟨N', hN'⟩ →ₗ[locRing B' x'] stalk B' x' T')

/-- Transport between base changes of equal lattices over the local ring at `x'`. -/
private abbrev Tr (hNN' : N = N') :
    latticeBaseChange 𝒪 K (locRing B' x') ⟨N, hN⟩ ≃ₗ[locRing B' x']
      latticeBaseChange 𝒪 K (locRing B' x') ⟨N', hN'⟩ :=
  transportEquiv (locRing B' x') (M₁ := ⟨N, hN⟩) (M₂ := ⟨N', hN'⟩) hNN'

/-- Base change along `locMap f x'`. -/
private abbrev rT : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩ →ₗ[𝒪]
    latticeBaseChange 𝒪 K (locRing B' x') ⟨N, hN⟩ :=
  LinearMap.rTensor (↥N) (locMap f x').toLinearMap

omit [Module.Invertible B T] [Module.Invertible B' T'] in
private theorem comm_all (hNN' : N = N')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N) (hv' : v ∈ N') (t : T) (s : B)
      (hs : f s ∉ x'.asIdeal),
      u ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N)) =
        LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
      u' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N')) =
        LocalizedModule.mk (τ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl))
    (z : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩) :
    u' (Tr x' hN hN' hNN' (rT f x' hN z)) = stalkMap f x' τ (u z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    rw [LinearMap.map_add, LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add,
      stalkMap_add, ha, hb]
  | tmul r v =>
    obtain ⟨t, s, hts⟩ := exists_mk (u ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] v))
    have hv' : (v : Fin 2 → K) ∈ N' := hNN' ▸ v.2
    have hs : f (s : B) ∉ x'.asIdeal := s.2
    have key := hu v v.2 hv' t s hs (by rw [← hts])
    have hl : Tr x' hN hN' hNN' (rT f x' hN (r ⊗ₜ[𝒪] v)) =
        locMap f x' r • ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨(v : Fin 2 → K), hv'⟩ : ↥N')) := by
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Tr]
      erw [transportEquiv_tmul]
      have hofEq : (LinearEquiv.ofEq _ _ hNN' v : ↥(⟨N', hN'⟩ : FullLattice 𝒪 K).1) =
          ⟨(v : Fin 2 → K), hv'⟩ :=
        Subtype.ext rfl
      rw [hofEq, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hr : (r ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩) =
        r • ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hl, map_smul, hr, map_smul, stalkMap_smul, ← hts, stalkMap_mk, key]

private theorem ker_transfer (hNN' : N = N') (hu'surj : Function.Surjective u')
    (husurj : Function.Surjective u)
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N) (hv' : v ∈ N') (t : T) (s : B)
      (hs : f s ∉ x'.asIdeal),
      u ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N)) =
        LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
      u' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N')) =
        LocalizedModule.mk (τ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl))
    (d : DeligneDatum (K := K) π B)
    (hker : LinearMap.ker u = (d.map π (toLocRing B (pointUnder f x'))).line ⟨N, hN⟩) :
    LinearMap.ker u' = ((d.map π f).map π (toLocRing B' x')).line ⟨N', hN'⟩ := by
  have hRHS : ((d.map π f).map π (toLocRing B' x')).line ⟨N', hN'⟩ =
      (lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u)).map
        (Tr x' hN hN' hNN').toLinearMap := by
    have h1 := DeligneDatum.line_transport π ((d.map π f).map π (toLocRing B' x'))
      (M₁ := ⟨N, hN⟩) (M₂ := ⟨N', hN'⟩) hNN'
    rw [h1, map_map_toLocRing π f x' d, hker]
    rfl
  have hcomm : ∀ z, (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) (rT f x' hN z) =
      stalkMap f x' τ (u z) :=
    fun z => comm_all f x' hN hN' τ u u' hNN' hu z
  have hle : lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) ≤
      LinearMap.ker (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hz' : u z = 0 := hz
    have := hcomm z
    rw [hz', stalkMap_zero] at this
    exact this
  have hInvQ : Module.Invertible (locRing B (pointUnder f x'))
      (latticeBaseChange 𝒪 K (locRing B (pointUnder f x')) ⟨N, hN⟩ ⧸ LinearMap.ker u) :=
    Module.Invertible.congr (u.quotKerEquivOfSurjective husurj).symm
  have hInv' : Module.Invertible (locRing B' x')
      (latticeBaseChange 𝒪 K (locRing B' x') ⟨N, hN⟩ ⧸
        lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u)) :=
    invertible_quotient_lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) hInvQ
  have hsurj'' : Function.Surjective (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) := by
    intro m
    obtain ⟨z, rfl⟩ := hu'surj m
    exact ⟨(Tr x' hN hN' hNN').symm z, by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]⟩
  have hbij : Function.Bijective
      ((lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u)).liftQ
        (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) hle) := by
    apply Module.Invertible.bijective_of_surjective
    intro m
    obtain ⟨z, rfl⟩ := hsurj'' m
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hge : LinearMap.ker (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) ≤
      lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) := by
    have h1 := LinearMap.ker_eq_bot_of_injective hbij.injective
    rw [Submodule.ker_liftQ] at h1
    have h2 := (LinearMap.le_ker_iff_map).mpr h1
    rwa [Submodule.ker_mkQ] at h2
  have hker'' : LinearMap.ker (u' ∘ₗ (Tr x' hN hN' hNN').toLinearMap) =
      lineBaseChange (locMap f x') ⟨N, hN⟩ (LinearMap.ker u) := le_antisymm hge hle
  rw [hRHS, ← hker'', LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective]
  exact (Tr x' hN hN' hNN').surjective

end Kernel

private theorem edgeNondegAt_map (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B')
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π (pointUnder f x').asIdeal M' M) :
    (d.map π f).EdgeNondegAt π x'.asIdeal M' M := by
  obtain ⟨hle, hπ, h1, h2⟩ := h
  refine ⟨hle, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) x'.asIdeal _
      (h1 v hv)
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') x'.asIdeal _
      (h2 v' hv')

end QuadNat

/-- A base change of a quadruple of `d` is a quadruple of the base change of `d`. -/
theorem IsQuadrupleOf.map_of_isBaseChangeAlong
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'}
    {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (hf : Q.IsBaseChangeAlong f Q') : Q'.IsQuadrupleOf (d.map π f) := by
  obtain ⟨β⟩ := hf
  intro x'
  obtain ⟨hedge, hk₀, hk₁⟩ := h (pointUnder f x')
  have hL₀ : Q'.L₀ x' = Q.L₀ (pointUnder f x') := Subtype.ext (β.N₀_eq x')
  have hL₁ : Q'.L₁ x' = Q.L₁ (pointUnder f x') := Subtype.ext (β.N₁_eq x')
  refine ⟨?_, ?_, ?_⟩
  · rw [hL₀, hL₁]; exact QuadNat.edgeNondegAt_map π f x' d _ _ hedge
  · exact QuadNat.ker_transfer π f x' (Q.full₀ (pointUnder f x')) (Q'.full₀ x') β.τ₀
      (Q.u₀ (pointUnder f x')) (Q'.u₀ x') (β.N₀_eq x').symm (Q'.u₀_surjective x')
      (Q.u₀_surjective _) (fun v hv hv' t s hs => β.u₀_eq x' v hv hv' t s hs) d hk₀
  · exact QuadNat.ker_transfer π f x' (Q.full₁ (pointUnder f x')) (Q'.full₁ x') β.τ₁
      (Q.u₁ (pointUnder f x')) (Q'.u₁ x') (β.N₁_eq x').symm (Q'.u₁_surjective x')
      (Q.u₁_surjective _) (fun v hv hv' t s hs => β.u₁_eq x' v hv hv' t s hs) d hk₁

namespace QuadAway

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

private theorem tmul_mem_map_line_sup (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B)
    (𝔮 : Ideal B') (M : FullLattice 𝒪 K) (v : ↥M.1)
    (h : (1 : B) ⊗ₜ[𝒪] v ∈
      d.line M ⊔ (Ideal.comap f 𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    (1 : B') ⊗ₜ[𝒪] v ∈
      (d.map π f).line M ⊔ (𝔮 • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  rw [← rTensor_one_tmul f M v]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
  rw [← hab, map_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · change _ ∈ lineBaseChange f M (d.line M)
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  · refine Submodule.smul_induction_on hb (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · rw [rTensor_smul_left f M r n]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hx hy

private theorem edgeNondegAt_of_map (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B)
    (𝔮 : Ideal B') (M' M : FullLattice 𝒪 K) (h : (d.map π f).EdgeNondegAt π 𝔮 M' M) :
    d.EdgeNondegAt π (Ideal.comap f 𝔮) M' M := by
  obtain ⟨hle, hπ, h1, h2⟩ := h
  exact ⟨hle, hπ, fun v hv hmem => h1 v hv (tmul_mem_map_line_sup f d 𝔮 M v hmem),
    fun v' hv' hmem => h2 v' hv' (tmul_mem_map_line_sup f d 𝔮 M' v' hmem)⟩

private theorem exists_not_mem {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (x : PrimeSpectrum B) : ∃ i : Fin k, f i ∉ x.asIdeal := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply x.isPrime.ne_top
  rw [eq_top_iff, ← hf]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)

private theorem comap_toAlgHom (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C]
    [IsScalarTower 𝒪 B C] (I : Ideal C) :
    Ideal.comap (IsScalarTower.toAlgHom 𝒪 B C) I = Ideal.comap (algebraMap B C) I :=
  Ideal.ext fun _ => Iff.rfl

private theorem ker_eq_line {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C]
    [IsScalarTower 𝒪 B C] (g : B) [IsLocalization.Away g C]
    (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C)
    (d : DeligneDatum (K := K) π B) (N N' : FullLattice 𝒪 K) (hN : N = N')
    (u : latticeBaseChange 𝒪 K (locRing B (LocBC.pt B y)) N →ₗ[locRing B (LocBC.pt B y)]
      stalk B (LocBC.pt B y) T)
    (u' : latticeBaseChange 𝒪 K (locRing C y) N' →ₗ[locRing C y] stalk C y T')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N.1) (hv' : v ∈ N'.1) (t : T) (s : B)
      (hs : algebraMap B C s ∉ y.asIdeal),
      u ((1 : locRing B (LocBC.pt B y)) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N.1)) =
        LocalizedModule.mk t ⟨s, hs⟩ →
      u' ((1 : locRing C y) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N'.1)) =
        LocalizedModule.mk (τ t) ⟨algebraMap B C s, hs⟩)
    (hker' : LinearMap.ker u' =
      ((d.map π (IsScalarTower.toAlgHom 𝒪 B C)).map π (toLocRing C y)).line N') :
    LinearMap.ker u = (d.map π (toLocRing B (LocBC.pt B y))).line N := by
  subst hN
  let _ : Module B T' := Module.compHom T' (algebraMap B C)
  have : IsScalarTower B C T' := ⟨fun b c t => by
    change (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower 𝒪 B (locRing C y) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply 𝒪 C (locRing C y), IsScalarTower.algebraMap_apply 𝒪 B C]
    rfl)
  have : IsLocalization.AtPrime (locRing C y) (LocBC.pt B y).asIdeal :=
    LocBC.isLocalization_atPrime_locRing (Submonoid.powers g) y
  have hγ := LocBC.isLocalizedModule_γ (Submonoid.powers g) T T' τ hτ y
  have hψ : (toLocRing C y).comp (IsScalarTower.toAlgHom 𝒪 B C) =
      IsScalarTower.toAlgHom 𝒪 B (locRing C y) :=
    AlgHom.ext fun _ => rfl
  have hker'' : LinearMap.ker u' =
      lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (locRing C y)) N (d.line N) := by
    rw [hker', ← hψ]
    exact congrArg (fun e : DeligneDatum (K := K) π (locRing C y) => e.line N)
      (DeligneDatum.map_comp π (IsScalarTower.toAlgHom 𝒪 B C) (toLocRing C y) d).symm
  have hsq : ∀ p₀ : latticeBaseChange 𝒪 K B N,
      u' (LocBC.ιB (locRing C y) N p₀) =
        IsLocalizedModule.iso (LocBC.pt B y).asIdeal.primeCompl (LocBC.γ 𝒪 T T' τ y)
          (u (LocBC.ιB (locRing B (LocBC.pt B y)) N p₀)) := by
    intro p₀
    induction p₀ using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b v =>
      have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B N) = b • ((1 : B) ⊗ₜ[𝒪] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have l1 : LocBC.ιB (locRing C y) N (b ⊗ₜ[𝒪] v) = b • ((1 : locRing C y) ⊗ₜ[𝒪] v) := by
        rw [e1, map_smul, LocBC.ιB_one_tmul]
      have l2 : LocBC.ιB (locRing B (LocBC.pt B y)) N (b ⊗ₜ[𝒪] v) =
          b • ((1 : locRing B (LocBC.pt B y)) ⊗ₜ[𝒪] v) := by
        rw [e1, map_smul, LocBC.ιB_one_tmul]
      rw [l1, l2, LinearMap.map_smul_of_tower u', LinearMap.map_smul_of_tower u, map_smul]
      congr 1
      generalize hm : u ((1 : locRing B (LocBC.pt B y)) ⊗ₜ[𝒪] v) = m
      induction m using LocalizedModule.induction_on with
      | h t s =>
        rw [hu v.1 v.2 v.2 t s s.2 hm,
          LocBC.iso_γ_mk (Submonoid.powers g) T T' τ hτ y t s s.2]
  have hpt : ∀ p₀ : latticeBaseChange 𝒪 K B N,
      u (LocBC.ιB (locRing B (LocBC.pt B y)) N p₀) = 0 ↔
        LocBC.ιB (locRing B (LocBC.pt B y)) N p₀ ∈
          (d.map π (toLocRing B (LocBC.pt B y))).line N := by
    intro p₀
    rw [← (IsLocalizedModule.iso (LocBC.pt B y).asIdeal.primeCompl
        (LocBC.γ 𝒪 T T' τ y)).map_eq_zero_iff, ← hsq, ← LinearMap.mem_ker, hker'',
      LocBC.ιB_mem_lineBaseChange_iff (LocBC.pt B y).asIdeal.primeCompl N (d.line N) p₀]
    exact (LocBC.ιB_mem_lineBaseChange_iff (A := locRing B (LocBC.pt B y))
      (LocBC.pt B y).asIdeal.primeCompl N (d.line N) p₀).symm
  have := LocBC.isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B (LocBC.pt B y))
    (LocBC.pt B y).asIdeal.primeCompl N
  ext p
  obtain ⟨⟨p₀, s⟩, hsp⟩ := IsLocalizedModule.surj (LocBC.pt B y).asIdeal.primeCompl
    (LocBC.ιB (locRing B (LocBC.pt B y)) N) p
  have hunit : IsUnit (algebraMap B (locRing B (LocBC.pt B y)) s) :=
    IsLocalization.map_units (locRing B (LocBC.pt B y)) s
  have hsp' : algebraMap B (locRing B (LocBC.pt B y)) s • p =
      LocBC.ιB (locRing B (LocBC.pt B y)) N p₀ := by
    rw [algebraMap_smul, ← Submonoid.smul_def]; exact hsp
  have hinv : ((hunit.unit⁻¹ : (locRing B (LocBC.pt B y))ˣ) : locRing B (LocBC.pt B y)) •
      (algebraMap B (locRing B (LocBC.pt B y)) s • p) = p := by
    rw [smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]
  rw [LinearMap.mem_ker]
  constructor
  · intro hp
    have h0 : u (LocBC.ιB (locRing B (LocBC.pt B y)) N p₀) = 0 := by
      rw [← hsp', map_smul, hp, smul_zero]
    have hmem := (hpt p₀).mp h0
    rw [← hsp'] at hmem
    rw [← hinv]
    exact Submodule.smul_mem _ _ hmem
  · intro hp
    have hmem : LocBC.ιB (locRing B (LocBC.pt B y)) N p₀ ∈
        (d.map π (toLocRing B (LocBC.pt B y))).line N := by
      rw [← hsp']; exact Submodule.smul_mem _ _ hp
    have h0 := (hpt p₀).mpr hmem
    rw [← hsp', map_smul] at h0
    have h1 : u p = ((hunit.unit⁻¹ : (locRing B (LocBC.pt B y))ˣ) :
        locRing B (LocBC.pt B y)) • (algebraMap B (locRing B (LocBC.pt B y)) s • u p) := by
      rw [smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]
    rw [h1, h0, smul_zero]

end QuadAway

/-- Being a quadruple of `d` can be checked on the localizations away from a family of elements
generating the unit ideal. -/
theorem isQuadrupleOf_of_forall_isBaseChangeAlong_away
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
    (hf : Ideal.span (Set.range f) = ⊤)
    (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
    (Qf : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hbc : ∀ i : Fin k,
      Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Qf i))
    (hQf : ∀ i : Fin k,
      (Qf i).IsQuadrupleOf (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    Q.IsQuadrupleOf d := by
  classical
  intro x
  obtain ⟨i, hi⟩ := QuadAway.exists_not_mem f hf x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (f i)]; exact hi
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨W⟩ := hbc i
  obtain ⟨hedge, hker₀, hker₁⟩ := hQf i y
  have hL₀ : (Qf i).L₀ y = Q.L₀ (LocBC.pt B y) := Subtype.ext (W.N₀_eq y)
  have hL₁ : (Qf i).L₁ y = Q.L₁ (LocBC.pt B y) := Subtype.ext (W.N₁_eq y)
  refine ⟨?_, ?_, ?_⟩
  · rw [hL₀, hL₁] at hedge
    have h := QuadAway.edgeNondegAt_of_map
      (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) d y.asIdeal _ _ hedge
    rwa [QuadAway.comap_toAlgHom] at h
  · exact QuadAway.ker_eq_line (f i) Q.T₀ (Qf i).T₀ W.τ₀ W.span_range_τ₀ y d _ _ hL₀.symm
      (Q.u₀ _) ((Qf i).u₀ y) (W.u₀_eq y) hker₀
  · exact QuadAway.ker_eq_line (f i) Q.T₁ (Qf i).T₁ W.τ₁ W.span_range_τ₁ y d _ _ hL₁.symm
      (Q.u₁ _) ((Qf i).u₁ y) (W.u₁_eq y) hker₁

end CerednikDrinfeld.FormalOmega.DrinfeldDatum

end
