/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`,
`Definitions/
  Def_GoodReductionJacobian_RelativeGroupLawBaseChange.lean`,
`Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_charZero.lean`,
`Theorems/
  Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_isReduced_stalk_one_of_isAlgClosed.lean`,
`Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_stalk_one_of_charZero.lean`,
`Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_charZero.lean`,
`Theorems/
  Thm_GoodReductionJacobian_RelativeGroupLaw_forall_exists_sub_algebraMap_mem_and_exists_
  derivation_stalk_one.lean`
and the corresponding `P2M/Sol/S_*.lean` proof files
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

public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.GeometricallyReduced
public import MathlibExt.RingTheory.LocalRing.IsReducedOfDerivation
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Pullbacks

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Reducedness and smoothness of relative group laws in characteristic zero

A scheme that is locally of finite type over a field of characteristic zero
and carries a relative group law is reduced, and its structure morphism is
smooth. Smoothness needs the finite-type hypothesis, since a smooth morphism
is locally of finite presentation. Over an algebraically closed field,
reducedness of such a scheme follows from reducedness of the stalk at the
identity, because translation by a closed point moves the identity stalk to
the stalk at that point. Reducedness of the identity stalk in characteristic
zero is proved through derivations: a tangent functional at the identity,
viewed as a dual-number point, is translated by the group law to a derivation
of the stalk, and a Noetherian local ring with enough derivations is reduced.

Base change of relative group laws, used to pass to an algebraic closure, is
in `MathlibExt.AlgebraicGeometry.RelativeGroupLaw`. The auxiliary
declarations of the proofs are private to this file.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace HomogRedAux

theorem isReduced_of_forall_isClosed {X : Scheme.{u}} [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X :=
      by

  have haff : ∀ (U : X.Opens) (hU : IsAffineOpen U), _root_.IsReduced Γ(X, U) := by
    intro U hU
    apply isReduced_ofLocalizationMaximal
    intro J hJ
    let y : PrimeSpectrum Γ(X, U) := ⟨J, hJ.isPrime⟩
    have hy : hU.fromSpec y ∈ U := show hU.fromSpec y ∈ (U : Set X) from hU.range_fromSpec ▸
      Set.mem_range_self y

    have hyc : IsClosed ({hU.fromSpec y} : Set X) := by
      have h1 : IsClosed ({y} : Set (PrimeSpectrum Γ(X, U))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 hJ
      have h2 := hU.fromSpec.isOpenEmbedding.preimage_closedPoints (Y := X)
      have : y ∈ hU.fromSpec.base ⁻¹' closedPoints X := by rw [h2]; exact h1
      exact this
    have hred := h _ hyc
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
    haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) J :=
      hU.isLocalization_stalk' y hy
    let e := (IsLocalization.algEquiv J.primeCompl (Localization.AtPrime J) (X.presheaf.stalk
      (hU.fromSpec y)))
    exact isReduced_of_injective e.toRingHom e.injective

  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    haveI := haff U hU
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
    exact @isReduced_localizationPreserves _ _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) _ _
      hloc (haff U hU)
  exact isReduced_of_isReduced_stalk X

end HomogRedAux

namespace RelativeGroupLawDerivationAux

open TrivSqZeroExt

section LocalDual

variable {A : Type u} [CommRing A] [IsLocalRing A]

scoped instance isLocalRing_tsze : IsLocalRing (TrivSqZeroExt A A) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl (isUnit_iff_isUnit_fst.mpr h)
    · exact Or.inr (isUnit_iff_isUnit_fst.mpr (by simpa using h))

end LocalDual

section Tangent

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

theorem phi_algebraMap (φ : A →ₗ[k] k) (hφ1 : φ 1 = 0) (c : k) : φ (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, hφ1, smul_zero]

theorem phi_mul (ρ : A →ₐ[k] k) (I : Ideal A) (hρ : ∀ a, a - algebraMap k A (ρ a) ∈ I)
    (φ : A →ₗ[k] k) (hφ1 : φ 1 = 0) (hφ2 : ∀ a b, a ∈ I → b ∈ I → φ (a * b) = 0) (a b : A) :
    φ (a * b) = ρ a * φ b + ρ b * φ a := by
  have h := hφ2 _ _ (hρ a) (hρ b)
  have expand : (a - algebraMap k A (ρ a)) * (b - algebraMap k A (ρ b)) =
      a * b - ((ρ a) • b + (ρ b) • a) + algebraMap k A (ρ a * ρ b) := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [expand, map_add, map_sub, map_add, LinearMap.map_smul, LinearMap.map_smul,
    phi_algebraMap φ hφ1] at h
  simp only [smul_eq_mul, add_zero] at h
  linear_combination h

def tangentHom (ρ : A →ₐ[k] k) (I : Ideal A) (hρ : ∀ a, a - algebraMap k A (ρ a) ∈ I)
    (φ : A →ₗ[k] k) (hφ1 : φ 1 = 0) (hφ2 : ∀ a b, a ∈ I → b ∈ I → φ (a * b) = 0) :
    A →ₐ[k] DualNumber k where
  toFun a := inl (ρ a) + inr (φ a)
  map_one' := by ext <;> simp [hφ1]
  map_mul' a b := by
    ext
    · simp
    · simp [phi_mul ρ I hρ φ hφ1 hφ2 a b, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_add_add_comm]
  commutes' c := by
    ext
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp [Algebra.algebraMap_eq_smul_one, hφ1]

@[scoped simp] theorem fst_tangentHom (ρ : A →ₐ[k] k) (I : Ideal A) (hρ : ∀ a, a - algebraMap k A (ρ
  a) ∈ I)
    (φ : A →ₗ[k] k) (hφ1 : φ 1 = 0) (hφ2 : ∀ a b, a ∈ I → b ∈ I → φ (a * b) = 0) (a : A) :
    (tangentHom ρ I hρ φ hφ1 hφ2 a).fst = ρ a := by
  simp [tangentHom]

@[scoped simp] theorem snd_tangentHom (ρ : A →ₐ[k] k) (I : Ideal A) (hρ : ∀ a, a - algebraMap k A (ρ
  a) ∈ I)
    (φ : A →ₗ[k] k) (hφ1 : φ 1 = 0) (hφ2 : ∀ a b, a ∈ I → b ∈ I → φ (a * b) = 0) (a : A) :
    (tangentHom ρ I hρ φ hφ1 hφ2 a).snd = φ a := by
  simp [tangentHom]

end Tangent

section DerivOfHom

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

def derivationOfHom (q : A →ₐ[k] TrivSqZeroExt A A) (hq : ∀ a, (q a).fst = a) : Derivation k A A
  where
  toFun a := (q a).snd
  map_add' a b := by simp
  map_smul' c a := by
    show (q (c • a)).snd = c • (q a).snd
    rw [map_smul, snd_smul]
  map_one_eq_zero' := by simp
  leibniz' a b := by
    have := congrArg TrivSqZeroExt.snd (map_mul q a b)
    simp only [snd_mul, hq, smul_eq_mul] at this
    show (q (a * b)).snd = a • (q b).snd + b • (q a).snd
    rw [this]; simp [smul_eq_mul, MulOpposite.smul_eq_mul_unop]; ring

end DerivOfHom

section SchemePart

open CategoryTheory AlgebraicGeometry IsLocalRing

variable (k : Type u) [Field k] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of k)) (L :
  RelativeGroupLaw k g)

noncomputable abbrev eMor : Spec (CommRingCat.of k) ⟶ G := (L.one (𝟙 _)).left

theorem eMor_over : eMor k g L ≫ g = 𝟙 _ := by simpa using (L.one (𝟙 _)).w

noncomputable abbrev ePt : ↥G := eMor k g L (closedPoint k)

noncomputable def ι : CommRingCat.of k ⟶ G.presheaf.stalk (ePt k g L) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop ≫ G.presheaf.germ ⊤ (ePt k g L) trivial

theorem Spec_ι : Spec.map (ι k g L) = G.fromSpecStalk (ePt k g L) ≫ g := by
  have h1 : g = G.toSpecΓ ≫ Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
    by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have h2 : G.fromSpecStalk (ePt k g L) ≫ g =
      (G.fromSpecStalk (ePt k g L) ≫ G.toSpecΓ) ≫ Spec.map g.appTop ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [Category.assoc, ← h1]
  rw [h2, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp]
  simp only [ι, Category.assoc]

noncomputable def ρ₀ : G.presheaf.stalk (ePt k g L) ⟶ CommRingCat.of k :=
  Scheme.stalkClosedPointTo (eMor k g L)

scoped instance : IsLocalHom (ρ₀ k g L).hom := Scheme.isLocalHom_stalkClosedPointTo' _

theorem Spec_ρ₀ : Spec.map (ρ₀ k g L) ≫ G.fromSpecStalk (ePt k g L) = eMor k g L :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

theorem ι_ρ₀ : ι k g L ≫ ρ₀ k g L = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_id, Spec_ι, ← Category.assoc, Spec_ρ₀, eMor_over]

theorem ρ₀_ι (c : k) : (ρ₀ k g L).hom ((ι k g L).hom c) = c := by
  have := congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f.hom c) (ι_ρ₀ k g L)
  simpa [CommRingCat.hom_comp] using this

theorem mem_maximalIdeal_of_map_eq_zero {A : Type u} [CommRing A] [IsLocalRing A] {K : Type u}
  [Field K]
    (f : A →+* K) [IsLocalHom f] (a : A) (h : f a = 0) : a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := hu.map f
  rw [h] at this
  exact not_isUnit_zero this

theorem sub_ι_ρ₀_mem (a : G.presheaf.stalk (ePt k g L)) :
    a - (ι k g L).hom ((ρ₀ k g L).hom a) ∈ maximalIdeal (G.presheaf.stalk (ePt k g L)) :=
  mem_maximalIdeal_of_map_eq_zero (ρ₀ k g L).hom _ (by rw [map_sub, ρ₀_ι, sub_self])

end SchemePart

section DualMaps

open CategoryTheory AlgebraicGeometry IsLocalRing TrivSqZeroExt

def tszeMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [smul_eq_mul, MulOpposite.smul_eq_mul_unop]; try ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[scoped simp] theorem fst_tszeMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x :
  TrivSqZeroExt R R) :
    (tszeMap f x).fst = f x.fst := by simp [tszeMap]

@[scoped simp] theorem snd_tszeMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x :
  TrivSqZeroExt R R) :
    (tszeMap f x).snd = f x.snd := by simp [tszeMap]

theorem tszeMap_comp_apply {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g
  : S →+* T)
    (x : TrivSqZeroExt R R) : tszeMap g (tszeMap f x) = tszeMap (g.comp f) x := by
  ext <;> simp

theorem isLocalHom_tszeMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f] :
    IsLocalHom (tszeMap f) := by
  constructor
  intro x hx
  rw [isUnit_iff_isUnit_fst] at hx ⊢
  rw [fst_tszeMap] at hx
  exact IsLocalHom.map_nonunit _ hx

theorem isLocalHom_fstHom {R : Type u} [CommRing R] :
    IsLocalHom (TrivSqZeroExt.fstHom R R R).toRingHom := by
  constructor
  intro x hx
  exact isUnit_iff_isUnit_fst.mpr hx

end DualMaps

section Points

open CategoryTheory AlgebraicGeometry IsLocalRing TrivSqZeroExt

variable (k : Type u) [Field k] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of k)) (L :
  RelativeGroupLaw k g)

noncomputable abbrev Aε : CommRingCat.{u} :=
  CommRingCat.of (TrivSqZeroExt ↑(G.presheaf.stalk (ePt k g L)) ↑(G.presheaf.stalk (ePt k g L)))

scoped instance : IsLocalRing ↑(Aε k g L) := isLocalRing_tsze

noncomputable def inclA : G.presheaf.stalk (ePt k g L) ⟶ Aε k g L :=
  CommRingCat.ofHom (TrivSqZeroExt.inlHom ↑(G.presheaf.stalk (ePt k g L)) ↑(G.presheaf.stalk (ePt k
    g L)))

theorem isLocalHom_comp' {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (g' : S →+* T) (f :
  R →+* S)
    (hg : IsLocalHom g') (hf : IsLocalHom f) : IsLocalHom (g'.comp f) :=
  ⟨fun a ha => hf.map_nonunit a (hg.map_nonunit _ ha)⟩

noncomputable def fstA : Aε k g L ⟶ G.presheaf.stalk (ePt k g L) :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom ↑(G.presheaf.stalk (ePt k g L)) ↑(G.presheaf.stalk (ePt k
    g L))
    ↑(G.presheaf.stalk (ePt k g L))).toRingHom

scoped instance : IsLocalHom (fstA k g L).hom := isLocalHom_fstHom

noncomputable def jK : CommRingCat.of (DualNumber k) ⟶ Aε k g L := CommRingCat.ofHom (tszeMap (ι k g
  L).hom)

noncomputable def jres : Aε k g L ⟶ CommRingCat.of (DualNumber k) := CommRingCat.ofHom (tszeMap (ρ₀
  k g L).hom)

scoped instance : IsLocalHom (jres k g L).hom := isLocalHom_tszeMap _

def inclK : CommRingCat.of k ⟶ CommRingCat.of (DualNumber k) :=
  CommRingCat.ofHom (algebraMap k (DualNumber k))

@[scoped simp] theorem inclA_apply (a : G.presheaf.stalk (ePt k g L)) : (inclA k g L).hom a = inl a
  := rfl
@[scoped simp] theorem fstA_apply (x : Aε k g L) : (fstA k g L).hom x = x.fst := rfl
@[scoped simp] theorem jK_apply (x : DualNumber k) : (jK k g L).hom x = tszeMap (ι k g L).hom x :=
  rfl
@[scoped simp] theorem jres_apply (x : Aε k g L) : (jres k g L).hom x = tszeMap (ρ₀ k g L).hom x :=
  rfl
@[scoped simp] theorem inclK_apply (c : k) : (inclK k).hom c = inl c := by
  show algebraMap k (DualNumber k) c = inl c
  rw [TrivSqZeroExt.algebraMap_eq_inl']; simp

theorem inclA_fstA : inclA k g L ≫ fstA k g L = 𝟙 _ :=
  CommRingCat.hom_ext (RingHom.ext fun a => by
    simp only [inclA, fstA]
    exact TrivSqZeroExt.fst_inl (↑(G.presheaf.stalk (ePt k g L))) a)

theorem jK_jres : jK k g L ≫ jres k g L = 𝟙 _ :=
  CommRingCat.hom_ext (RingHom.ext fun x => by
    change tszeMap (ρ₀ k g L).hom (tszeMap (ι k g L).hom x) = x
    rw [tszeMap_comp_apply]
    apply TrivSqZeroExt.ext
    · rw [fst_tszeMap, RingHom.comp_apply, ρ₀_ι]
    · rw [snd_tszeMap, RingHom.comp_apply, ρ₀_ι])

theorem inclA_jres : inclA k g L ≫ jres k g L = ρ₀ k g L ≫ inclK k :=
  CommRingCat.hom_ext (RingHom.ext fun a => by
    change tszeMap (ρ₀ k g L).hom (inl a) = algebraMap k (DualNumber k) ((ρ₀ k g L).hom a)
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    apply TrivSqZeroExt.ext <;> simp)

theorem ι_inclA_jres : ι k g L ≫ inclA k g L ≫ jres k g L = inclK k := by
  rw [inclA_jres, ← Category.assoc, ι_ρ₀, Category.id_comp]

theorem stalk_hom_ext {R : CommRingCat.{u}} [IsLocalRing R] (x : ↥G)
    (f₁ f₂ : G.presheaf.stalk x ⟶ R) (h₁ : IsLocalHom f₁.hom) (h₂ : IsLocalHom f₂.hom)
    (h : Spec.map f₁ ≫ G.fromSpecStalk x = Spec.map f₂ ≫ G.fromSpecStalk x) : f₁ = f₂ := by
  have := (SpecToEquivOfLocalRing G R).symm.injective
    (a₁ := ⟨x, f₁, h₁⟩) (a₂ := ⟨x, f₂, h₂⟩) h
  exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)

variable (τ' : G.presheaf.stalk (ePt k g L) ⟶ CommRingCat.of (DualNumber k)) [IsLocalHom τ'.hom]
  (hτfst : ∀ a, (τ'.hom a).fst = (ρ₀ k g L).hom a) (hτι : ∀ c : k, τ'.hom ((ι k g L).hom c) = inl c)

noncomputable def tA : Spec (G.presheaf.stalk (ePt k g L)) ⟶ Spec (CommRingCat.of k) :=
  G.fromSpecStalk (ePt k g L) ≫ g

noncomputable def tT : Spec (Aε k g L) ⟶ Spec (CommRingCat.of k) := Spec.map (inclA k g L) ≫ tA k g
  L

noncomputable def tK : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of k) := Spec.map
  (inclK k)

noncomputable def P₁ : (Over.mk (tT k g L) ⟶ Over.mk g) :=
  Over.homMk (Spec.map (inclA k g L) ≫ G.fromSpecStalk (ePt k g L)) (by
    simp only [Over.mk_hom, tT, tA, Category.assoc])

noncomputable def tpt : Spec (CommRingCat.of (DualNumber k)) ⟶ G := Spec.map τ' ≫ G.fromSpecStalk
  (ePt k g L)

include hτι in
theorem ι_τ' : ι k g L ≫ τ' = inclK k :=
  CommRingCat.hom_ext (RingHom.ext fun c => by
    change τ'.hom ((ι k g L).hom c) = algebraMap k (DualNumber k) c
    rw [hτι, TrivSqZeroExt.algebraMap_eq_inl']; simp)

include hτι in
theorem tpt_over : tpt k g L τ' ≫ g = tK k := by
  rw [tpt, Category.assoc, ← Spec_ι, ← Spec.map_comp, ι_τ' k g L τ' hτι]; rfl

include hτι in
noncomputable def P₂ : (Over.mk (tT k g L) ⟶ Over.mk g) :=
  Over.homMk (Spec.map (jK k g L) ≫ tpt k g L τ') (by
    have h1 : (Spec.map (jK k g L) ≫ tpt k g L τ') ≫ g = tT k g L := by
      rw [Category.assoc, tpt_over k g L τ' hτι, tK, tT, tA, ← Spec_ι,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun c => by
        change tszeMap (ι k g L).hom (algebraMap k (DualNumber k) c) =
          inl ((ι k g L).hom c)
        rw [TrivSqZeroExt.algebraMap_eq_inl']
        apply TrivSqZeroExt.ext <;> simp)
    simpa only [Over.mk_hom] using h1)

noncomputable def Q : Spec (Aε k g L) ⟶ G := (L.mul (tT k g L) (P₁ k g L) (P₂ k g L τ' hτι)).left

theorem Q_over : Q k g L τ' hτι ≫ g = tT k g L :=
  (L.mul (tT k g L) (P₁ k g L) (P₂ k g L τ' hτι)).w

theorem mul_left_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of k)} (h : t₁ = t₂)
    (P Q : Over.mk t₁ ⟶ Over.mk g) (P' Q' : Over.mk t₂ ⟶ Over.mk g) (hP : P.left = P'.left) (hQ :
      Q.left = Q'.left) :
    (L.mul t₁ P Q).left = (L.mul t₂ P' Q').left := by
  subst h
  obtain rfl : P = P' := Over.OverMorphism.ext hP
  obtain rfl : Q = Q' := Over.OverMorphism.ext hQ
  rfl

theorem one_coe (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) : (L.one t).left = t ≫ eMor k g L
  := by
  have := L.one_natural (𝟙 _) t t (Category.comp_id _)
  rw [← this]; rfl

include hτfst hτι in

theorem fstA_Q : Spec.map (fstA k g L) ≫ Q k g L τ' hτι = G.fromSpecStalk (ePt k g L) := by
  have hψ : Spec.map (fstA k g L) ≫ tT k g L = tA k g L := by
    rw [tT, ← Category.assoc, ← Spec.map_comp, inclA_fstA, Spec.map_id, Category.id_comp]
  have nat := congrArg (fun φ => φ.left) (L.mul_natural (tT k g L) (tA k g L) (Spec.map (fstA k g
    L)) hψ
    (P₁ k g L) (P₂ k g L τ' hτι))
  simp only [Over.comp_left, Over.homMk_left] at nat
  show Spec.map (fstA k g L) ≫ (L.mul (tT k g L) (P₁ k g L) (P₂ k g L τ' hτι)).left = _
  rw [nat]
  have e1 : ((Over.homMk (U := Over.mk (tA k g L)) (V := Over.mk (tT k g L))
      (Spec.map (fstA k g L)) hψ ≫ P₁ k g L)).left = G.fromSpecStalk (ePt k g L)
    := by
    show Spec.map (fstA k g L) ≫ Spec.map (inclA k g L) ≫ G.fromSpecStalk (ePt k g L) = _
    rw [← Category.assoc, ← Spec.map_comp, inclA_fstA, Spec.map_id, Category.id_comp]
  have e2 : (Over.homMk (Spec.map (fstA k g L)) hψ ≫ P₂ k g L τ' hτι).left = (L.one (tA k g L)).left
    := by
    rw [one_coe]
    show Spec.map (fstA k g L) ≫ Spec.map (jK k g L) ≫ Spec.map τ' ≫ G.fromSpecStalk (ePt k g L) = _
    have : τ' ≫ jK k g L ≫ fstA k g L = ρ₀ k g L ≫ ι k g L :=
      CommRingCat.hom_ext (RingHom.ext fun a => by
        change (tszeMap (ι k g L).hom (τ'.hom a)).fst = (ι k g L).hom ((ρ₀ k g L).hom a)
        rw [fst_tszeMap, hτfst])
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, this, Spec.map_comp_assoc, Spec_ρ₀, Spec_ι];
      rfl
  rw [mul_left_congr k g L rfl
    (Over.homMk (U := Over.mk (tA k g L)) (V := Over.mk (tT k g L)) (Spec.map (fstA k g L)) hψ ≫
      P₁ k g L)
    (Over.homMk (U := Over.mk (tA k g L)) (V := Over.mk (tT k g L)) (Spec.map (fstA k g L)) hψ ≫
      P₂ k g L τ' hτι)
    (Over.homMk (U := Over.mk (tA k g L)) (V := Over.mk g) (G.fromSpecStalk (ePt k g L)) rfl)
    (L.one (tA k g L)) e1 e2, L.mul_one]
  rfl

include hτfst hτι in

theorem jres_Q : Spec.map (jres k g L) ≫ Q k g L τ' hτι = tpt k g L τ' := by
  have hψ : Spec.map (jres k g L) ≫ tT k g L = tK k := by
    rw [tT, tA, ← Spec_ι, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ι_inclA_jres]; rfl
  have nat := congrArg (fun φ => φ.left) (L.mul_natural (tT k g L) (tK k) (Spec.map (jres k g L)) hψ
    (P₁ k g L) (P₂ k g L τ' hτι))
  simp only [Over.comp_left, Over.homMk_left] at nat
  show Spec.map (jres k g L) ≫ (L.mul (tT k g L) (P₁ k g L) (P₂ k g L τ' hτι)).left = _
  rw [nat]
  have e1 : ((Over.homMk (Spec.map (jres k g L)) hψ ≫ P₁ k g L)).left = (L.one (tK k)).left := by
    rw [one_coe]
    show Spec.map (jres k g L) ≫ Spec.map (inclA k g L) ≫ G.fromSpecStalk (ePt k g L) = _
    rw [← Category.assoc, ← Spec.map_comp, inclA_jres, Spec.map_comp, Category.assoc, Spec_ρ₀]; rfl
  have e2 : (Over.homMk (U := Over.mk (tK k)) (V := Over.mk (tT k g L))
      (Spec.map (jres k g L)) hψ ≫ P₂ k g L τ' hτι).left = tpt k g L τ' := by
    show Spec.map (jres k g L) ≫ Spec.map (jK k g L) ≫ tpt k g L τ' = _
    rw [← Category.assoc, ← Spec.map_comp, jK_jres, Spec.map_id, Category.id_comp]
  rw [mul_left_congr k g L rfl
    (Over.homMk (U := Over.mk (tK k)) (V := Over.mk (tT k g L)) (Spec.map (jres k g L)) hψ ≫
      P₁ k g L)
    (Over.homMk (U := Over.mk (tK k)) (V := Over.mk (tT k g L)) (Spec.map (jres k g L)) hψ ≫
      P₂ k g L τ' hτι) (L.one (tK k))
    (Over.homMk (U := Over.mk (tK k)) (V := Over.mk g) (tpt k g L τ')
      (tpt_over k g L τ' hτι)) e1 e2, L.one_mul]
  rfl

include hτfst hτι in
theorem Q_closedPoint : Q k g L τ' hτι (closedPoint ↑(Aε k g L)) = ePt k g L := by
  have h1 := congrArg (fun f : Spec (CommRingCat.of (DualNumber k)) ⟶ G =>
      f (closedPoint ↑(CommRingCat.of (DualNumber k)))) (jres_Q k g L τ' hτfst hτι)
  set_option backward.isDefEq.respectTransparency.types false in
  rw [Scheme.Hom.comp_apply, Spec_closedPoint] at h1
  unfold tpt at h1
  set_option backward.isDefEq.respectTransparency.types false in
  rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] at h1
  exact h1

include hτfst hτι in

theorem exists_ψ : ∃ (ψ : G.presheaf.stalk (ePt k g L) ⟶ Aε k g L) (_ : IsLocalHom ψ.hom),
    ψ ≫ fstA k g L = 𝟙 _ ∧ ψ ≫ jres k g L = τ' ∧ ι k g L ≫ ψ = ι k g L ≫ inclA k g L := by
  obtain ⟨⟨x, ψ, hψl⟩, hQ⟩ := (SpecToEquivOfLocalRing G (Aε k g L)).symm.surjective (Q k g L τ' hτι)
  have hQ' : Spec.map ψ ≫ G.fromSpecStalk x = Q k g L τ' hτι := hQ
  have hx : x = ePt k g L := by
    haveI := hψl
    have h1 := congrArg (fun f : Spec (Aε k g L) ⟶ G =>
        f (closedPoint ↑(Aε k g L))) hQ'
    set_option backward.isDefEq.respectTransparency.types false in
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint,
      Q_closedPoint k g L τ' hτfst hτι] at h1
    exact h1
  subst hx
  refine ⟨ψ, hψl, ?_, ?_, ?_⟩
  · apply stalk_hom_ext (ePt k g L) (ψ ≫ fstA k g L) (𝟙 _)
      (by rw [CommRingCat.hom_comp]; exact isLocalHom_comp' _ _ inferInstance hψl)
      (by rw [CommRingCat.hom_id]; exact ⟨fun _ h => h⟩)
    rw [Spec.map_comp, Category.assoc, hQ', fstA_Q k g L τ' hτfst hτι, Spec.map_id,
      Category.id_comp]
  · apply stalk_hom_ext (ePt k g L) (ψ ≫ jres k g L) τ'
      (by rw [CommRingCat.hom_comp]; exact isLocalHom_comp' _ _ inferInstance hψl) inferInstance
    rw [Spec.map_comp, Category.assoc, hQ', jres_Q k g L τ' hτfst hτι, tpt]
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec_ι, ← Category.assoc, hQ', Q_over]
    rfl

end Points

section Assembly

open CategoryTheory AlgebraicGeometry IsLocalRing TrivSqZeroExt

variable (k : Type u) [Field k] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of k)) (L :
  RelativeGroupLaw k g)

theorem main [Algebra k ↑(G.presheaf.stalk (ePt k g L))]
    (halg : ∀ c : k, algebraMap k ↑(G.presheaf.stalk (ePt k g L)) c = (ι k g L).hom c)
    (φ : ↑(G.presheaf.stalk (ePt k g L)) →ₗ[k] k)
    (h2 : ∀ a ∈ (maximalIdeal ↑(G.presheaf.stalk (ePt k g L))) ^ 2, φ a = 0)
    (h1 : ∀ c : k, φ (algebraMap k ↑(G.presheaf.stalk (ePt k g L)) c) = 0) :
    ∃ D : Derivation k ↑(G.presheaf.stalk (ePt k g L)) ↑(G.presheaf.stalk (ePt k g L)),
      ∀ a, D a - algebraMap k _ (φ a) ∈ maximalIdeal ↑(G.presheaf.stalk (ePt k g L)) := by

  have hρc : ∀ c : k, (ρ₀ k g L).hom (algebraMap k _ c) = algebraMap k k c := fun c => by
    rw [halg, ρ₀_ι, Algebra.algebraMap_self, RingHom.id_apply]
  let ρ : ↑(G.presheaf.stalk (ePt k g L)) →ₐ[k] k := ⟨(ρ₀ k g L).hom, hρc⟩
  have hρ : ∀ a, a - algebraMap k _ (ρ a) ∈ maximalIdeal ↑(G.presheaf.stalk (ePt k g L)) := fun a =>
    by
    rw [halg]; exact sub_ι_ρ₀_mem k g L a
  have hφ1 : φ 1 = 0 := by simpa using h1 1
  have hφ2 : ∀ a b, a ∈ maximalIdeal ↑(G.presheaf.stalk (ePt k g L)) →
      b ∈ maximalIdeal ↑(G.presheaf.stalk (ePt k g L)) → φ (a * b) = 0 :=
    fun a b ha hb => h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)
  let τ := tangentHom ρ (maximalIdeal _) hρ φ hφ1 hφ2
  let τ' : G.presheaf.stalk (ePt k g L) ⟶ CommRingCat.of (DualNumber k) := CommRingCat.ofHom
    τ.toRingHom
  haveI hτl : IsLocalHom τ'.hom := by
    constructor
    intro a ha
    have h := isUnit_iff_isUnit_fst.mp ha
    change IsUnit (τ a).fst at h
    rw [fst_tangentHom] at h
    exact IsLocalHom.map_nonunit (f := (ρ₀ k g L).hom) a h
  have hτfst : ∀ a, (τ'.hom a).fst = (ρ₀ k g L).hom a := fun a => by
    show (τ a).fst = _; rw [fst_tangentHom]; rfl
  have hτι : ∀ c : k, τ'.hom ((ι k g L).hom c) = inl c := fun c => by
    show τ ((ι k g L).hom c) = inl c
    rw [← halg, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl']; simp
  obtain ⟨ψ, hψl, hfst, hres, hι⟩ := exists_ψ k g L τ' hτfst hτι

  have hqc : ∀ c : k, ψ.hom (algebraMap k _ c) =
      algebraMap k (TrivSqZeroExt ↑(G.presheaf.stalk (ePt k g L)) ↑(G.presheaf.stalk (ePt k g L))) c
        := fun c => by
    rw [TrivSqZeroExt.algebraMap_eq_inl', halg]
    have := congrArg (fun f : CommRingCat.of k ⟶ Aε k g L => f.hom c) hι
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  let q : ↑(G.presheaf.stalk (ePt k g L)) →ₐ[k]
      TrivSqZeroExt ↑(G.presheaf.stalk (ePt k g L)) ↑(G.presheaf.stalk (ePt k g L)) := ⟨ψ.hom, hqc⟩
  have hq : ∀ a, (q a).fst = a := fun a => by
    have := congrArg (fun f : G.presheaf.stalk (ePt k g L) ⟶ G.presheaf.stalk (ePt k g L) => f.hom
      a) hfst
    simp [CommRingCat.hom_comp] at this
    exact this
  refine ⟨derivationOfHom q hq, fun a => ?_⟩
  show (ψ.hom a).snd - algebraMap k _ (φ a) ∈ _
  rw [halg]
  apply mem_maximalIdeal_of_map_eq_zero (ρ₀ k g L).hom
  have := congrArg (fun f : G.presheaf.stalk (ePt k g L) ⟶ CommRingCat.of (DualNumber k) => (f.hom
    a).snd) hres
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  change (tszeMap (ρ₀ k g L).hom (ψ.hom a)).snd = (τ a).snd at this
  rw [snd_tszeMap, snd_tangentHom] at this
  rw [map_sub, this, ρ₀_ι, sub_self]

end Assembly

end RelativeGroupLawDerivationAux


namespace RelativeGroupLaw

/-- Over an algebraically closed field, a scheme with a relative group law
that is locally of finite type and whose stalk at the identity is reduced
is reduced. -/
public theorem isReduced_of_isReduced_stalk_one_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (he : _root_.IsReduced (G.presheaf.stalk
      ((L.one (𝟙 (Spec (CommRingCat.of k)))).left (IsLocalRing.closedPoint k)))) :
    IsReduced G := by
  classical
  letI : GrpObj (Over.mk g) := L.grpObjOverMk
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace g
  apply HomogRedAux.isReduced_of_forall_isClosed
  intro x hx
  let e' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk g :=
    L.one (𝟙 (Spec (CommRingCat.of k)))
  let x' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk g :=
    Over.homMk (pointOfClosedPoint g x hx) (pointOfClosedPoint_comp g x hx)
  let α := (GrpObj.mulRight (A := Over.mk g) e').symm ≪≫ (GrpObj.mulRight (A := Over.mk g) x')
  have hα : e' ≫ α.hom = x' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp only [GrpObj.mulRight_inv, CartesianMonoidalCategory.comp_lift_assoc,
      Category.comp_id, ← Category.assoc,
      SemiCartesianMonoidalCategory.comp_toUnit,
      SemiCartesianMonoidalCategory.toUnit_unit, Category.id_comp,
      GrpObj.lift_comp_inv_right]
    simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
      SemiCartesianMonoidalCategory.comp_toUnit, SemiCartesianMonoidalCategory.toUnit_unit,
      Category.id_comp, GrpObj.lift_comp_inv_right]
    have htu : SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
      SemiCartesianMonoidalCategory.toUnit_unit
    simp only [htu, Category.id_comp, GrpObj.lift_comp_inv_right]
  have hα' : α.hom.left ((L.one (𝟙 (Spec (CommRingCat.of k)))).left
      (IsLocalRing.closedPoint k)) = x := by
    have h1 := congr(($hα).left (IsLocalRing.closedPoint k))
    simp only [e', x', Over.comp_left, Over.homMk_left, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.comp_apply] at h1
    refine h1.trans ?_
    exact pointOfClosedPoint_apply g x hx _
  let β : G ≅ G := (Over.forget _).mapIso α
  have hβ : β.hom = α.hom.left := rfl
  rw [← hα', ← hβ]
  have hst : IsIso (β.hom.stalkMap ((L.one (𝟙 (Spec (CommRingCat.of k)))).left
      (IsLocalRing.closedPoint k))) := inferInstance
  exact isReduced_of_injective (β.hom.stalkMap _).hom
    ((ConcreteCategory.isIso_iff_bijective _).1 hst).1

/-- At the identity of a relative group law on a scheme locally of finite type
over a field, every element of the stalk differs from a constant by an element
of the maximal ideal, and every cotangent functional at the identity lifts to
a derivation of the stalk. -/
public theorem forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one
    (k : Type u) [Field k] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType g] (L : RelativeGroupLaw k g) :
    let e : ↥G := (L.one (𝟙 (Spec (CommRingCat.of k)))).left (IsLocalRing.closedPoint k)
    letI : Algebra k (G.presheaf.stalk e) :=
      ((G.presheaf.germ ⊤ e trivial).hom.comp
        (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
    (∀ a : G.presheaf.stalk e, ∃ c : k, a - algebraMap k (G.presheaf.stalk e) c ∈
      IsLocalRing.maximalIdeal (G.presheaf.stalk e)) ∧
    ∀ φ : (G.presheaf.stalk e) →ₗ[k] k,
      (∀ a ∈ (IsLocalRing.maximalIdeal (G.presheaf.stalk e)) ^ 2, φ a = 0) →
      (∀ c : k, φ (algebraMap k (G.presheaf.stalk e) c) = 0) →
      ∃ D : Derivation k (G.presheaf.stalk e) (G.presheaf.stalk e),
        ∀ a : G.presheaf.stalk e, D a - algebraMap k (G.presheaf.stalk e) (φ a) ∈
          IsLocalRing.maximalIdeal (G.presheaf.stalk e) := by
  intro e
  letI instAlg : Algebra k (G.presheaf.stalk e) :=
    ((G.presheaf.germ ⊤ e trivial).hom.comp
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
  have halg : ∀ c : k, algebraMap k (G.presheaf.stalk
      (RelativeGroupLawDerivationAux.ePt k g L)) c =
      (RelativeGroupLawDerivationAux.ι k g L).hom c := fun c => rfl
  refine ⟨fun a => ⟨(RelativeGroupLawDerivationAux.ρ₀ k g L).hom a, ?_⟩,
    fun φ h2 h1 => RelativeGroupLawDerivationAux.main k g L halg φ h2 h1⟩
  rw [halg]
  exact RelativeGroupLawDerivationAux.sub_ι_ρ₀_mem k g L a

/-- The stalk at the identity of a relative group law on a scheme locally of
finite type over a field of characteristic zero is reduced. -/
public theorem isReduced_stalk_one_of_charZero
    (k : Type u) [Field k] [CharZero k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    _root_.IsReduced (G.presheaf.stalk
      ((L.one (𝟙 (Spec (CommRingCat.of k)))).left (IsLocalRing.closedPoint k))) := by
  let e : ↥G := (L.one (𝟙 (Spec (CommRingCat.of k)))).left (IsLocalRing.closedPoint k)
  letI alg : Algebra k (G.presheaf.stalk e) :=
    ((G.presheaf.germ ⊤ e trivial).hom.comp
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
  obtain ⟨hk, hder⟩ := L.forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one k g
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero k (G.presheaf.stalk e) hk hder

/-- A scheme locally of finite type over a field of characteristic zero that
carries a relative group law is reduced. -/
public theorem isReduced_of_charZero
    (k : Type u) [Field k] [CharZero k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    IsReduced G := by
  let K : Type u := AlgebraicClosure k
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let L' : RelativeGroupLaw K (baseChangeStr ι g) := L.baseChange ι
  haveI : LocallyOfFiniteType (baseChangeStr ι g) := inferInstance
  have he := L'.isReduced_stalk_one_of_charZero K (baseChangeStr ι g)
  haveI hred : IsReduced (baseChangeScheme ι g) :=
    L'.isReduced_of_isReduced_stalk_one_of_isAlgClosed K (baseChangeStr ι g) he
  haveI : Flat g := inferInstance
  haveI : QuasiCompact ι := inferInstance
  haveI : IsSchemeTheoreticallyDominant ι := by
    rw [isSchemeTheoreticallyDominant_iff_isDominant]
    infer_instance
  haveI : IsSchemeTheoreticallyDominant (pullback.fst g ι) := inferInstance
  haveI : QuasiCompact (pullback.fst g ι) := inferInstance
  haveI : IsReduced (pullback g ι) := hred
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst g ι)

/-- A scheme locally of finite type over a field of characteristic zero that
carries a relative group law is smooth over the field. The finite-type
hypothesis cannot be dropped, since a smooth morphism is locally of finite
presentation. -/
public theorem smooth_of_charZero
    (k : Type u) [Field k] [CharZero k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    Smooth g := by
  letI : GrpObj (Over.mk g) := L.grpObjOverMk
  haveI : IsReduced G := L.isReduced_of_charZero k g
  haveI : GeometricallyReduced g :=
    GeometricallyReduced.of_isReduced_of_perfectField g
  exact smooth_of_grpObj g

end RelativeGroupLaw

end AlgebraicGeometry
