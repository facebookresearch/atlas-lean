/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BurnsidePaqbReduction
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Complex.Basic
public import Mathlib.RepresentationTheory.FinGroupCharZero
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

import Mathlib.RepresentationTheory.Maschke

/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/

open CategoryTheory

namespace BurnsidePaqb

@[expose] public section

variable (G : Type) [Group G] [Fintype G]

omit [Fintype G] in
/-- The group order is nonzero in `ℂ`. -/
instance [Finite G] : NeZero (Nat.card G : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)⟩

/-- The group order is invertible in `ℂ`. -/
noncomputable instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (NeZero.ne _)

omit [Fintype G] in
/-- Bridge (forward): an irreducible complex representation gives a simple `FDRep`. -/
theorem simple_fdrep_of_irreducible {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Finite G] (σ : Representation ℂ G V) [σ.IsIrreducible] :
    Simple (FDRep.of σ) := by
  rw [FDRep.simple_iff_end_is_rank_one]
  have e1 := Representation.linHom.invariantsEquivFDRepHom (FDRep.of σ) (FDRep.of σ)
  have e2 := Representation.invariantsEquivIntertwiningMap (FDRep.of σ).ρ (FDRep.of σ).ρ
  rw [← LinearEquiv.finrank_eq e1, LinearEquiv.finrank_eq e2]
  change Module.finrank ℂ (σ.IntertwiningMap σ) = 1
  exact Representation.IsIrreducible.finrank_intertwiningMap_self σ

omit [Fintype G] in
/-- Bridge (reverse), auxiliary form with the representation named. -/
theorem irreducible_of_simple_fdrep_aux (V : FDRep ℂ G) [Simple V] [Finite G]
    (σ : Representation ℂ G V)
    (hσ : (V.ρ : Representation ℂ G V) = σ) :
    σ.IsIrreducible := by
  have h1 : Module.finrank ℂ (V ⟶ V) = 1 :=
    (FDRep.simple_iff_end_is_rank_one V).mp inferInstance
  have e1 := Representation.linHom.invariantsEquivFDRepHom V V
  rw [hσ] at e1
  have e2 := Representation.invariantsEquivIntertwiningMap σ σ
  have e3 := Representation.IntertwiningMap.equivAlgEnd (ρ := σ)
  have hEnd : Module.finrank ℂ (Module.End (MonoidAlgebra ℂ G) σ.asModule) = 1 := by
    calc Module.finrank ℂ (Module.End (MonoidAlgebra ℂ G) σ.asModule)
        = Module.finrank ℂ (σ.IntertwiningMap σ) :=
          (LinearEquiv.finrank_eq e3.toLinearEquiv).symm
      _ = Module.finrank ℂ ↥(Representation.linHom σ σ).invariants :=
          (LinearEquiv.finrank_eq e2).symm
      _ = Module.finrank ℂ (V ⟶ V) := LinearEquiv.finrank_eq e1
      _ = 1 := h1
  rw [Representation.irreducible_iff_isSimpleModule_asModule σ, isSimpleModule_iff]
  have h1nt : Nontrivial (V ⟶ V) := ⟨0, 𝟙 V, Ne.symm (id_nonzero V)⟩
  obtain ⟨f, g, hfg⟩ := h1nt
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ g x := by
    by_contra hcon
    push Not at hcon
    exact hfg (ConcreteCategory.hom_ext f g hcon)
  have hMnt : Nontrivial σ.asModule := ⟨f x, g x, hx⟩
  have hlat : Nontrivial (Submodule (MonoidAlgebra ℂ G) σ.asModule) := by
    obtain ⟨a, b, hab⟩ := hMnt
    refine ⟨⊥, ⊤, fun hcon => hab ?_⟩
    have ha : a ∈ (⊥ : Submodule (MonoidAlgebra ℂ G) σ.asModule) := by
      rw [hcon]; exact Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule (MonoidAlgebra ℂ G) σ.asModule) := by
      rw [hcon]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  refine IsSimpleOrder.of_forall_eq_top fun N hN => ?_
  obtain ⟨Q, hQ⟩ := MonoidAlgebra.Submodule.exists_isCompl N
  -- projections along the complement, as algebra-linear endomorphisms
  set pN : Module.End (MonoidAlgebra ℂ G) σ.asModule :=
    (Submodule.prodEquivOfIsCompl N Q hQ).toLinearMap ∘ₗ LinearMap.prodMap
      LinearMap.id 0 ∘ₗ
      (Submodule.prodEquivOfIsCompl N Q hQ).symm.toLinearMap with hpN
  set pQ : Module.End (MonoidAlgebra ℂ G) σ.asModule :=
    (Submodule.prodEquivOfIsCompl N Q hQ).toLinearMap ∘ₗ LinearMap.prodMap
      0 LinearMap.id ∘ₗ
      (Submodule.prodEquivOfIsCompl N Q hQ).symm.toLinearMap with hpQ
  have hidemN : pN ∘ₗ pN = pN := by
    apply LinearMap.ext; intro x
    simp [hpN, LinearMap.prodMap_apply]
  have hmul : pN ∘ₗ pQ = 0 := by
    apply LinearMap.ext; intro x
    simp [hpN, hpQ, LinearMap.prodMap_apply]
  have hidN : ∀ y : ↥N, pN (↑y : σ.asModule) = ↑y := by
    intro y
    have h1 : (Submodule.prodEquivOfIsCompl N Q hQ).symm.toLinearMap (↑y : σ.asModule)
        = (y, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left N Q hQ y
    have h2 : (Submodule.prodEquivOfIsCompl N Q hQ).toLinearMap ((y, 0) : ↥N × ↥Q)
        = ↑y := by
      simp
    simp only [hpN, LinearMap.comp_apply, LinearMap.prodMap_apply, h1,
      LinearMap.id_apply, LinearMap.zero_apply, h2]
  have hNne : pN ≠ 0 := by
    obtain ⟨y, hyN, hym⟩ : ∃ y ∈ N, (y : σ.asModule) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hN
      rw [Submodule.eq_bot_iff]
      intro y hy
      simpa using hcon y hy
    intro hzero
    apply hym
    have hpy : pN (↑(⟨y, hyN⟩ : ↥N) : σ.asModule) = 0 := by rw [hzero]; rfl
    rw [hidN] at hpy
    simpa using hpy
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' pN hNne).mp hEnd pQ
  have hidemNfun : ∀ x, pN (pN x) = pN x := fun x => DFunLike.congr_fun hidemN x
  have hsmul : ∀ (y : σ.asModule) (c : ℂ), pN (c • y) = c • pN y := by
    intro y c
    have h := map_smul pN (algebraMap ℂ (MonoidAlgebra ℂ G) c) y
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul] at h
    exact h
  have hcpN : c • pN = 0 := by
    have hcp : pN ∘ₗ pQ = c • pN := by
      rw [← hc]
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, hsmul, hidemNfun]
    rw [hmul] at hcp
    exact hcp.symm
  rcases smul_eq_zero.mp hcpN with h | h
  · -- `c = 0`, so `pQ = 0` and `Q = ⊥`
    have hpQ0 : pQ = 0 := by rw [← hc, h, zero_smul]
    have hidQ : ∀ q : ↥Q, pQ (↑q : σ.asModule) = ↑q := by
      intro q
      have h1 : (Submodule.prodEquivOfIsCompl N Q hQ).symm.toLinearMap (↑q : σ.asModule)
          = (0, q) :=
        Submodule.prodEquivOfIsCompl_symm_apply_right N Q hQ q
      have h2 : (Submodule.prodEquivOfIsCompl N Q hQ).toLinearMap ((0, q) : ↥N × ↥Q)
          = ↑q := by
        simp
      simp only [hpQ, LinearMap.comp_apply, LinearMap.prodMap_apply, h1,
        LinearMap.id_apply, LinearMap.zero_apply, h2]
    have hQbot : Q = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro q hq
      have hpq : pQ (↑(⟨q, hq⟩ : ↥Q) : σ.asModule) = 0 := by rw [hpQ0]; rfl
      rw [hidQ] at hpq
      simpa using hpq
    rw [hQbot] at hQ
    rw [← sup_bot_eq N]
    exact IsCompl.sup_eq_top hQ
  · exact absurd h hNne

omit [Fintype G] in
/-- Bridge (reverse): the underlying representation of a simple `FDRep` is irreducible. -/
theorem irreducible_of_simple_fdrep (V : FDRep ℂ G) [Simple V] [Finite G] :
    Representation.IsIrreducible (V.ρ : Representation ℂ G V) :=
  irreducible_of_simple_fdrep_aux G V (V.ρ : Representation ℂ G V) rfl

/-- Isomorphism classes of simple `FDRep`s: two simples are related when isomorphic. -/
def Simple.isoSetoid : Setoid {V : FDRep ℂ G // Simple V} where
  r S T := Nonempty (S.1 ≅ T.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun h => h.elim fun i => ⟨i.symm⟩,
    fun h1 h2 => h1.elim fun i => h2.elim fun j => ⟨i.trans j⟩⟩

/-- Iso-classes of simple finite-dimensional complex representations. -/
def Irr : Type 1 := Quotient (Simple.isoSetoid G)

/-- Character of a class, well-defined by `FDRep.char_iso`. -/
noncomputable def Irr.charFun (c : Irr G) : G → ℂ :=
  Quotient.lift (fun S => S.1.character) (fun S T h => by
    obtain ⟨i⟩ := h
    exact FDRep.char_iso i) c

omit [Fintype G] in
theorem Irr.charFun_mk (S : {V : FDRep ℂ G // Simple V}) :
    Irr.charFun G (Quotient.mk _ S) = S.1.character := rfl

/-- Chosen representative bundle of a class. -/
noncomputable def Irr.repBundle (c : Irr G) : {V : FDRep ℂ G // Simple V} :=
  Quotient.out c

omit [Fintype G] in
theorem Irr.mk_repBundle (c : Irr G) : Quotient.mk _ (Irr.repBundle G c) = c :=
  Quotient.out_eq c

omit [Fintype G] in
theorem Irr.charFun_repBundle (c : Irr G) :
    (Irr.repBundle G c).1.character = Irr.charFun G c := by
  have h := Irr.charFun_mk G (Irr.repBundle G c)
  rw [Irr.mk_repBundle] at h
  exact h.symm

omit [Fintype G] in
/-- Characters separate iso-classes (via `FDRep.char_orthonormal`). -/
theorem Irr.charFun_inj [Finite G] : Function.Injective (Irr.charFun G) := by
  let _ : Fintype G := Fintype.ofFinite G
  intro a b hab
  obtain ⟨S, rfl⟩ := Quotient.exists_rep a
  obtain ⟨T, rfl⟩ := Quotient.exists_rep b
  rw [Irr.charFun_mk G, Irr.charFun_mk G] at hab
  have := S.2
  have := T.2
  have h2 := FDRep.char_orthonormal (k := ℂ) S.1 S.1
  rw [ite_eq_left ⟨Iso.refl _⟩] at h2
  have h3 := FDRep.char_orthonormal (k := ℂ) S.1 T.1
  rw [← hab, h2] at h3
  have hne : Nonempty (S.1 ≅ T.1) := by
    by_contra hcon
    rw [ite_eq_right hcon] at h3
    exact one_ne_zero h3
  exact (Quotient.eq).mpr hne

/-- The trivial representation is irreducible: submodules of `ℂ` are `⊥`/`⊤`. -/
instance trivial_isIrreducible : (Representation.trivial ℂ G ℂ).IsIrreducible :=
  @IsSimpleOrder.of_forall_eq_top _ _ _
    ⟨⊤, ⊥, fun h => by
      have htop : (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule
          = ⊤ := rfl
      have hbot : (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule
          = ⊥ := rfl
      have hsub : (⊤ : Submodule ℂ ℂ) = ⊥ := by rw [← htop, ← hbot, h]
      have h1 : (1 : ℂ) ∈ (⊤ : Submodule ℂ ℂ) := Submodule.mem_top
      rw [hsub] at h1
      simp at h1⟩
    fun U hU => by
      rcases eq_bot_or_eq_top U.toSubmodule with h | h
      · exfalso
        apply hU
        have hU' : U.toSubmodule
            = (⊥ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule := by
          rw [h]; rfl
        exact Subrepresentation.toSubmodule_injective hU'
      · have hU' : U.toSubmodule
            = (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)).toSubmodule := by
          rw [h]; rfl
        exact Subrepresentation.toSubmodule_injective hU'

/-- The iso-class of the trivial representation. -/
noncomputable def Irr.triv : Irr G :=
  Quotient.mk _
    ⟨FDRep.of (Representation.trivial ℂ G ℂ),
      simple_fdrep_of_irreducible G (Representation.trivial ℂ G ℂ)⟩

/-- The character of the trivial class is `1`. -/
theorem Irr.charFun_triv (g : G) : Irr.charFun G (Irr.triv G) g = 1 := by
  change (FDRep.of (Representation.trivial ℂ G ℂ)).character g = 1
  have hg : (FDRep.of (Representation.trivial ℂ G ℂ)).ρ g = LinearMap.id := rfl
  change LinearMap.trace ℂ ↥(FDRep.of (Representation.trivial ℂ G ℂ))
    ((FDRep.of (Representation.trivial ℂ G ℂ)).ρ g) = 1
  rw [hg, LinearMap.trace_id, Module.finrank_self, Nat.cast_one]

omit [Fintype G] in
/-- The character at `1` is the degree. -/
theorem Irr.charFun_one (c : Irr G) :
    Irr.charFun G c 1 = ((Module.finrank ℂ ↥(Irr.repBundle G c).1 : ℕ) : ℂ) := by
  have h := FDRep.char_one (Irr.repBundle G c).1
  rwa [Irr.charFun_repBundle] at h

omit [Fintype G] in
/-- Character of a class agrees with its bundled representation. -/
theorem Irr.charFun_eq_repBundle_char (c : Irr G) (x : G) :
    Irr.charFun G c x = Representation.character
      ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1) x := by
  rw [← Irr.charFun_repBundle]
  rfl

open Classical in
/-- Row orthogonality over iso-classes. -/
theorem charInner_orth (i j : Irr G) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, Irr.charFun G i g * Irr.charFun G j g⁻¹ =
      if i = j then 1 else 0 := by
  classical
  have := (Irr.repBundle G i).2
  have := (Irr.repBundle G j).2
  have hi := Irr.charFun_repBundle G i
  have hj := Irr.charFun_repBundle G j
  rw [← hi, ← hj]
  have h := FDRep.char_orthonormal (k := ℂ) (Irr.repBundle G i).1 (Irr.repBundle G j).1
  rw [h]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left ⟨Iso.refl _⟩]
  · rw [ite_eq_right hij, ite_eq_right]
    intro hcon
    apply hij
    obtain ⟨e⟩ := hcon
    have hq : Quotient.mk (Simple.isoSetoid G) (Irr.repBundle G i) =
        Quotient.mk (Simple.isoSetoid G) (Irr.repBundle G j) :=
      Quotient.eq.mpr ⟨e⟩
    rw [Irr.mk_repBundle, Irr.mk_repBundle] at hq
    exact hq

/-- Class functions: constant on conjugacy classes. -/
def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

/-- Every finite set of iso-classes has cardinality at most `|G|`. -/
theorem cardBound (s : Finset (Irr G)) : s.card ≤ Fintype.card G := by
  classical
  have hli : LinearIndependent ℂ (fun i : ↥s => Irr.charFun G (i : Irr G)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hfun : ∀ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) = 0 := by
      intro x
      have hcon := congrFun hg x
      simpa using hcon
    intro j
    have hexpand : (Nat.card G : ℂ)⁻¹ *
        ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹ = g j := by
      have step1 : ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹
          = ∑ i, g i * (∑ x : G, Irr.charFun G ((i : ↥s) : Irr G) x *
            Irr.charFun G ((j : ↥s) : Irr G) x⁻¹) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp [smul_eq_mul, mul_assoc]
      rw [step1, Finset.mul_sum]
      trans ∑ i : ↥s, (if ((i : ↥s) : Irr G) = (j : ↥s) then g i else 0)
      · refine Finset.sum_congr rfl fun i _ => ?_
        have hi := charInner_orth G ((i : ↥s) : Irr G) ((j : ↥s) : Irr G)
        rw [mul_left_comm, hi]
        by_cases hij : ((i : ↥s) : Irr G) = (j : ↥s)
        · rw [ite_eq_left hij, ite_eq_left hij, mul_one]
        · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
      · simp_rw [Subtype.ext_iff.symm]
        exact Fintype.sum_ite_eq' j g
    have h2 : (Nat.card G : ℂ)⁻¹ *
        ∑ x : G, (∑ i, g i • Irr.charFun G ((i : ↥s) : Irr G) x) *
          Irr.charFun G ((j : ↥s) : Irr G) x⁻¹ = 0 := by
      simp_rw [hfun, zero_mul, Finset.sum_const_zero, mul_zero]
    rw [hexpand] at h2
    exact h2
  have h := LinearIndependent.fintype_card_le_finrank hli
  rw [Module.finrank_pi] at h
  rwa [Fintype.card_coe] at h

omit [Fintype G] in
/-- Iso-classes form a finite type. -/
noncomputable instance [Finite G] : Finite (Irr G) := by
  let _ : Fintype G := Fintype.ofFinite G
  rw [← not_infinite_iff_finite]
  intro hInf
  have e := Infinite.natEmbedding (Irr G)
  set N := Fintype.card G
  have hcard := cardBound G (Finset.map e (Finset.range (N + 1)))
  rw [Finset.card_map, Finset.card_range] at hcard
  omega

noncomputable instance : Fintype (Irr G) := Fintype.ofFinite _

/-- Zimmerman's averaging operator for a function `f`. -/
noncomputable def zimmOp (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (f : G → ℂ) :
    Module.End ℂ M :=
  ∑ g : G, f g • (Representation.ofModule' (k := ℂ) M) g⁻¹

/-- The averaging operator commutes with the `G`-action for class functions. -/
theorem zimmOp_comm (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    (f : G → ℂ) (hf : IsClassFun G f) (h : G) (x : M) :
    (Representation.ofModule' (k := ℂ) M) h (zimmOp G M f x) =
      zimmOp G M f ((Representation.ofModule' (k := ℂ) M) h x) := by
  classical
  have hconj : ∀ u : G, f (u⁻¹ * h) = f (h * u⁻¹) := by
    intro u
    have h1 := hf (h * u⁻¹) u⁻¹
    rw [inv_inv] at h1
    have h2 : u⁻¹ * (h * u⁻¹) * u = u⁻¹ * h := by group
    rw [h2] at h1
    exact h1
  have eL_apply : ∀ u : G, (Equiv.inv G).trans (Equiv.mulRight h) u = u⁻¹ * h :=
    fun u => rfl
  have eR_apply : ∀ u : G, (Equiv.inv G).trans (Equiv.mulLeft h) u = h * u⁻¹ :=
    fun u => rfl
  have pushL : (Representation.ofModule' (k := ℂ) M) h
      (∑ g, f g • (Representation.ofModule' (k := ℂ) M) g⁻¹ x) =
      ∑ g, f g • (Representation.ofModule' (k := ℂ) M) (h * g⁻¹) x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul]
    congr 1
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, map_mul]
  have pushR : (∑ g, f g • (Representation.ofModule' (k := ℂ) M) g⁻¹
      ((Representation.ofModule' (k := ℂ) M) h x)) =
      ∑ g, f g • (Representation.ofModule' (k := ℂ) M) (g⁻¹ * h) x := by
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, map_mul]
  have reL : (∑ g, f g • (Representation.ofModule' (k := ℂ) M) (h * g⁻¹) x) =
      (∑ u, f (h * u⁻¹) • (Representation.ofModule' (k := ℂ) M) u x) := by
    rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight h))
      (fun g => f g • (Representation.ofModule' (k := ℂ) M) (h * g⁻¹) x)]
    refine Finset.sum_congr rfl fun u _ => ?_
    show f ((Equiv.inv G).trans (Equiv.mulRight h) u) •
        (Representation.ofModule' (k := ℂ) M)
          (h * ((Equiv.inv G).trans (Equiv.mulRight h) u)⁻¹) x = _
    rw [eL_apply]
    have harg : h * (u⁻¹ * h)⁻¹ = u := by group
    rw [harg, hconj u]
  have reR : (∑ g, f g • (Representation.ofModule' (k := ℂ) M) (g⁻¹ * h) x) =
      (∑ u, f (h * u⁻¹) • (Representation.ofModule' (k := ℂ) M) u x) := by
    rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft h))
      (fun g => f g • (Representation.ofModule' (k := ℂ) M) (g⁻¹ * h) x)]
    refine Finset.sum_congr rfl fun u _ => ?_
    show f ((Equiv.inv G).trans (Equiv.mulLeft h) u) •
        (Representation.ofModule' (k := ℂ) M)
          (((Equiv.inv G).trans (Equiv.mulLeft h) u)⁻¹ * h) x = _
    rw [eR_apply]
    have harg : (h * u⁻¹)⁻¹ * h = u := by group
    rw [harg]
  unfold zimmOp
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [pushL, pushR, reL, reR]

-- A simple algebra-module gives an irreducible representation.
omit [Fintype G] in
theorem irreducible_ofModule' (M : Type*) [AddCommGroup M]
    [Module (MonoidAlgebra ℂ G) M] [Module ℂ M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hAlg : (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom =
      Algebra.lsmul ℂ ℂ M := by
    simp only [Representation.asAlgebraHom_def, Representation.ofModule',
      Equiv.apply_symm_apply]
  have e : (Representation.ofModule' (k := ℂ) (G := G) M).asModule
      ≃ₗ[MonoidAlgebra ℂ G] M :=
    { toFun := fun x => (x : M),
      invFun := fun x => (x : (Representation.ofModule' (k := ℂ) (G := G) M).asModule),
      map_add' := fun _ _ => rfl, map_smul' := ?_,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  · refine IsSimpleModule.congr e
  · intro r x
    have h := Representation.asModuleEquiv_map_smul
      (ρ := Representation.ofModule' (k := ℂ) (G := G) M) r x
    rw [hAlg] at h
    simp only [Representation.asModuleEquiv, Algebra.lsmul_apply] at h
    exact h

-- Zimmerman's operator acts as a scalar on a simple module.
theorem zimmEigenScalar (M : Type) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [Module.Finite ℂ M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M]
    (f : G → ℂ) (hf : IsClassFun G f) :
    ∃ μ : ℂ, ∀ y : M, zimmOp G M f y = μ • y := by
  have hfin : FiniteDimensional ℂ M := inferInstance
  have hnt : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) M
  have hirr : (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible :=
    irreducible_ofModule' G M
  obtain ⟨μ, hμ⟩ := @Module.End.exists_eigenvalue ℂ M _ _ _ inferInstance hfin hnt
    (zimmOp G M f)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, fun y => ?_⟩
  let E : Subrepresentation (Representation.ofModule' (k := ℂ) (G := G) M) :=
    { toSubmodule := Module.End.eigenspace (zimmOp G M f) μ,
      apply_mem_toSubmodule := fun h y hy => by
        rw [Module.End.mem_eigenspace_iff] at hy ⊢
        have hcomm := zimmOp_comm G M f hf h y
        rw [← hcomm, hy, map_smul] }
  have hET : E = ⊤ := by
    rcases @eq_bot_or_eq_top _ _ _ hirr E with hbot | htop
    · exfalso
      have hmem : v ∈ E.toSubmodule := hv.1
      rw [hbot] at hmem
      exact hv.2 hmem
    · exact htop
  have hmem : y ∈ E.toSubmodule := by
    rw [hET]
    exact Submodule.mem_top
  exact Module.End.mem_eigenspace_iff.mp hmem

-- The averaging operator vanishes on simple modules for orthogonal class functions.
theorem zimmVanish (M : Type) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] [Module.Finite ℂ M]
    [IsSimpleModule (MonoidAlgebra ℂ G) M]
    (f : G → ℂ) (hf : IsClassFun G f)
    (horth : ∀ c : Irr G,
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹ = 0) :
    zimmOp G M f = 0 := by
  classical
  have hirr : (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible :=
    irreducible_ofModule' G M
  have hsimple : Simple (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)) :=
    simple_fdrep_of_irreducible G _
  obtain ⟨μ, hμ⟩ := zimmEigenScalar G M f hf
  have hchar : ∀ u : G, (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character u =
      LinearMap.trace ℂ M ((Representation.ofModule' (k := ℂ) (G := G) M) u) := fun u => rfl
  have horthC : (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g *
      (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹ = 0 := by
    have h := horth (Quotient.mk _
      ⟨FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M), hsimple⟩)
    rwa [Irr.charFun_mk] at h
  have hTr : LinearMap.trace ℂ M (zimmOp G M f) =
      ∑ g : G, f g * (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹ := by
    have h1 : ∀ g : G, LinearMap.trace ℂ M
        (f g • (Representation.ofModule' (k := ℂ) (G := G) M) g⁻¹) =
        f g * (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹ := by
      intro g
      rw [map_smul, ← hchar g⁻¹]
      simp only [smul_eq_mul]
    unfold zimmOp
    rw [map_sum]
    exact Finset.sum_congr rfl (fun g _ => h1 g)
  have hTr0 : LinearMap.trace ℂ M (zimmOp G M f) = 0 := by
    rw [hTr]
    have hne : (Nat.card G : ℂ) ≠ 0 := NeZero.ne _
    have h2 : (∑ g : G, f g *
        (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹) =
        (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g *
          (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)).character g⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h2, horthC, mul_zero]
  have hTmu : zimmOp G M f = μ • LinearMap.id := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact hμ y
  have hTrmu : LinearMap.trace ℂ M (zimmOp G M f) =
      μ • (Module.finrank ℂ M : ℂ) := by
    rw [hTmu, map_smul, LinearMap.trace_id]
  have hmu : μ = 0 := by
    have hfr : (Module.finrank ℂ M : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos_iff.mpr
        (IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) M)))
    rw [hTrmu] at hTr0
    simp only [smul_eq_mul] at hTr0
    exact (mul_eq_zero.mp hTr0).resolve_right hfr
  rw [hmu, zero_smul] at hTmu
  exact hTmu

-- Carrier of the regular module.
abbrev RegMod : Type := ↥(⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))

omit [Fintype G] in
theorem ofModule'_apply (M : Type) [AddCommGroup M] [Module (MonoidAlgebra ℂ G) M]
    [Module ℂ M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] (g : G) (x : M) :
    (Representation.ofModule' (k := ℂ) (G := G) M) g x =
      MonoidAlgebra.single g (1 : ℂ) • x := by
  simp [Representation.ofModule']

-- The kernel of the averaging operator is stable under the algebra action.
theorem zimmKerStab (f : G → ℂ) (hf : IsClassFun G f) (a : MonoidAlgebra ℂ G) :
    ∀ (x : RegMod G) (_ : zimmOp G (RegMod G) f x = 0),
      zimmOp G (RegMod G) f (a • x) = 0 := by
  refine MonoidAlgebra.induction_on
    (motive := fun a => ∀ (x : RegMod G) (_ : zimmOp G (RegMod G) f x = 0),
      zimmOp G (RegMod G) f (a • x) = 0) a ?_ ?_ ?_
  · intro g x hx
    rw [MonoidAlgebra.of_apply, ← ofModule'_apply G (RegMod G) g x,
      ← zimmOp_comm G (RegMod G) f hf g x, hx, map_zero]
  · intro a b ha hb x hx
    rw [add_smul, map_add, ha x hx, hb x hx, add_zero]
  · intro r a ha x hx
    rw [smul_assoc, map_smul, ha x hx, smul_zero]

-- The averaging operator vanishes on the regular module.
theorem zimmTopVanish {f : G → ℂ} (hf : IsClassFun G f)
    (horth : ∀ c : Irr G,
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹ = 0) :
    zimmOp G (RegMod G) f = 0 := by
  classical
  let K : Submodule (MonoidAlgebra ℂ G) (RegMod G) :=
    { carrier := {x | zimmOp G (RegMod G) f x = 0},
      add_mem' := by
        intro x y hx hy
        have hx' : zimmOp G (RegMod G) f x = 0 := hx
        have hy' : zimmOp G (RegMod G) f y = 0 := hy
        change zimmOp G (RegMod G) f (x + y) = 0
        rw [map_add, hx', hy', add_zero],
      zero_mem' := by
        change zimmOp G (RegMod G) f 0 = 0
        exact map_zero _,
      smul_mem' := by
        intro a x hx
        have hx' : zimmOp G (RegMod G) f x = 0 := hx
        change zimmOp G (RegMod G) f (a • x) = 0
        exact zimmKerStab G f hf a x hx' }
  set K_A : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    Submodule.map
      (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
      K with hKA
  obtain ⟨Q_A, hQA⟩ := MonoidAlgebra.Submodule.exists_isCompl K_A
  have hsub : ∀ S_A : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      [IsSimpleModule (MonoidAlgebra ℂ G) ↥S_A] → S_A ≤ Q_A → S_A ≤ K_A := by
    intro S_A hsimple hSQ t ht
    rw [hKA]
    refine Submodule.mem_map.mpr ⟨⟨t, Submodule.mem_top⟩, ?_, rfl⟩
    have hvan : zimmOp G ↥S_A f = 0 := zimmVanish G ↥S_A f hf horth
    have h0 : zimmOp G ↥S_A f ⟨t, ht⟩ = 0 := DFunLike.congr_fun hvan ⟨t, ht⟩
    have hsumA : (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
          (zimmOp G (RegMod G) f ⟨t, Submodule.mem_top⟩) =
        S_A.subtype (zimmOp G ↥S_A f ⟨t, ht⟩) := by
      unfold zimmOp
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      rw [map_sum (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) _ _,
        map_sum S_A.subtype _ _]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
      congr 1
    have hsub0 : (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
        (zimmOp G (RegMod G) f ⟨t, Submodule.mem_top⟩) = 0 := by
      rw [hsumA, h0, map_zero]
    have hker : zimmOp G (RegMod G) f ⟨t, Submodule.mem_top⟩ ∈
        LinearMap.ker (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) :=
      hsub0
    rw [Submodule.ker_subtype] at hker
    change zimmOp G (RegMod G) f (⟨t, Submodule.mem_top⟩ : RegMod G) = 0
    simpa using hker
  by_cases hQbot : Q_A = ⊥
  · have hKAtop : K_A = ⊤ := by
      have h := hQA.sup_eq_top
      rw [hQbot, sup_bot_eq] at h
      exact h
    apply LinearMap.ext
    intro y
    have hyA : ((y : RegMod G) : MonoidAlgebra ℂ G) ∈ K_A := by
      rw [hKAtop]
      exact Submodule.mem_top
    rw [hKA] at hyA
    obtain ⟨x, hxK, hxy⟩ := Submodule.mem_map.mp hyA
    have hxy' : x = y := Subtype.ext hxy
    rw [← hxy']
    exact hxK
  · exfalso
    have hex : ∃ S_A : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
        IsSimpleModule (MonoidAlgebra ℂ G) ↥S_A ∧ S_A ≤ Q_A := by
      by_contra hcon
      have hsup := IsSemisimpleModule.sSup_simples_le
        (R := MonoidAlgebra ℂ G) (M := MonoidAlgebra ℂ G) Q_A
      have hempty : {m : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) |
          IsSimpleModule (MonoidAlgebra ℂ G) ↥m ∧ m ≤ Q_A} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro m hmem
        exact hcon ⟨m, hmem⟩
      rw [hempty, sSup_empty] at hsup
      exact hQbot hsup.symm
    obtain ⟨S_A, hSsimple, hSQ⟩ := hex
    have hSK := hsub S_A hSQ
    have hle : S_A ≤ K_A ⊓ Q_A := le_inf hSK hSQ
    rw [hQA.inf_eq_bot] at hle
    have hSbot : S_A = ⊥ := le_bot_iff.mp hle
    have hntSA : Nontrivial ↥S_A :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ↥S_A
    obtain ⟨a, b, hab⟩ := hntSA
    subst hSbot
    have ha0 : (a : MonoidAlgebra ℂ G) = 0 :=
      (Submodule.mem_bot (MonoidAlgebra ℂ G)).mp a.2
    have hb0 : (b : MonoidAlgebra ℂ G) = 0 :=
      (Submodule.mem_bot (MonoidAlgebra ℂ G)).mp b.2
    exact hab (Subtype.ext (by rw [ha0, hb0]))

/-- Zimmerman Thm 5 core: a class function orthogonal to every irrep character is zero. -/
theorem classfun_eq_zero_of_orth {f : G → ℂ} (hf : IsClassFun G f)
    (horth : ∀ c : Irr G,
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹ = 0) :
    f = 0 := by
  classical
  have hTtop : zimmOp G (RegMod G) f = 0 := zimmTopVanish G hf horth
  have hpt : ∀ h : G, f h = 0 := by
    intro h
    have hT0 : zimmOp G (RegMod G) f
        ⟨MonoidAlgebra.single h 1, Submodule.mem_top⟩ = 0 :=
      DFunLike.congr_fun hTtop _
    have hA0 : ((zimmOp G (RegMod G) f
        ⟨MonoidAlgebra.single h 1, Submodule.mem_top⟩ : RegMod G) : MonoidAlgebra ℂ G) = 0 := by
      simp [hT0]
    have hexpand : ((zimmOp G (RegMod G) f
        ⟨MonoidAlgebra.single h 1, Submodule.mem_top⟩ : RegMod G) : MonoidAlgebra ℂ G) =
        ∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1:ℂ) := by
      change (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
        (zimmOp G (RegMod G) f _) = _
      unfold zimmOp
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      rw [map_sum (Submodule.subtype (⊤ : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) _ _]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.map_smul_of_tower, ofModule'_apply G (RegMod G) g⁻¹ _,
        LinearMap.map_smul_of_tower]
      congr 1
      change MonoidAlgebra.single g⁻¹ (1:ℂ) •
        ((⟨MonoidAlgebra.single h 1, Submodule.mem_top⟩ : RegMod G) : MonoidAlgebra ℂ G) = _
      simp only [smul_eq_mul, MonoidAlgebra.single_mul_single, mul_one]
    have hS0 : (∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1:ℂ)) = 0 :=
      hexpand.symm.trans hA0
    have h1 : (∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1:ℂ)).coeff 1 =
        ∑ g : G, f g • (if g⁻¹ * h = 1 then (1:ℂ) else 0) := by
      rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [MonoidAlgebra.coeff_smul_apply]
      congr 1
      exact Finsupp.single_apply
    have h2 : (∑ g : G, f g • MonoidAlgebra.single (g⁻¹ * h) (1:ℂ)).coeff 1 = 0 := by
      rw [hS0, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have hcoeff : (∑ g : G, f g • (if g⁻¹ * h = 1 then (1:ℂ) else 0)) = 0 :=
      h1.symm.trans h2
    have h9 : ∀ b : G, b ∈ Finset.univ → b ≠ h →
        f b • (if b⁻¹ * h = 1 then (1:ℂ) else 0) = 0 := by
      intro b _ hb
      have hne : b⁻¹ * h ≠ 1 := by
        intro hcon
        apply hb
        have h9 : b⁻¹ * h = b⁻¹ * b := by rw [hcon, inv_mul_cancel]
        exact (mul_left_cancel h9).symm
      rw [ite_eq_right hne, smul_zero]
    rw [Finset.sum_eq_single h h9 (fun hcon => absurd (Finset.mem_univ h) hcon)] at hcoeff
    rw [ite_eq_left (inv_mul_cancel h)] at hcoeff
    simpa using hcoeff
  exact funext hpt

omit [Fintype G] in
theorem Irr.charFun_classfun (c : Irr G) (g h : G) :
    Irr.charFun G c (h * g * h⁻¹) = Irr.charFun G c g := by
  obtain ⟨S, rfl⟩ := Quotient.exists_rep c
  exact FDRep.char_conj S.1 g h

/-- Expansion of a class function in the irrep-character basis (Zimmerman Prop 4 setup). -/
theorem classfun_expand {f : G → ℂ} (hf : IsClassFun G f) :
    f = ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) •
      Irr.charFun G c := by
  classical
  have hS : IsClassFun G (∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
      f g * Irr.charFun G c g⁻¹) • Irr.charFun G c) := by
    intro g h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Irr.charFun_classfun G c g h]
  have hD : IsClassFun G (f - ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
      f g * Irr.charFun G c g⁻¹) • Irr.charFun G c) := by
    intro g h
    rw [Pi.sub_apply, Pi.sub_apply, hf g h, hS g h]
  have horth : ∀ d : Irr G, (Nat.card G : ℂ)⁻¹ * ∑ g : G,
      (f - ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) •
        Irr.charFun G c) g * Irr.charFun G d g⁻¹ = 0 := by
    intro d
    have h2 : (∑ g : G, (f - ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
            f g * Irr.charFun G c g⁻¹) • Irr.charFun G c) g * Irr.charFun G d g⁻¹) =
        (∑ g : G, f g * Irr.charFun G d g⁻¹) -
          ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
            (∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹) := by
      have hstep : ∀ g : G, (f - ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
              f g * Irr.charFun G c g⁻¹) • Irr.charFun G c) g * Irr.charFun G d g⁻¹ =
          f g * Irr.charFun G d g⁻¹ -
            ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
              (Irr.charFun G c g * Irr.charFun G d g⁻¹) := by
        intro g
        have hS1 : (∑ x : Irr G, (((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G x g⁻¹) •
            Irr.charFun G x) g) * Irr.charFun G d g⁻¹ =
            ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
              (Irr.charFun G c g * Irr.charFun G d g⁻¹) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [Pi.sub_apply, Finset.sum_apply, sub_mul, hS1]
      calc (∑ g : G, (f - ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
                f g * Irr.charFun G c g⁻¹) • Irr.charFun G c) g * Irr.charFun G d g⁻¹)
          = ∑ g : G, (f g * Irr.charFun G d g⁻¹ -
              ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
                (Irr.charFun G c g * Irr.charFun G d g⁻¹)) :=
            Finset.sum_congr rfl fun g _ => hstep g
        _ = (∑ g : G, f g * Irr.charFun G d g⁻¹) -
              (∑ g : G, ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
                f g * Irr.charFun G c g⁻¹) * (Irr.charFun G c g * Irr.charFun G d g⁻¹)) :=
            Finset.sum_sub_distrib _ _
        _ = (∑ g : G, f g * Irr.charFun G d g⁻¹) -
              ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
                (∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹) := by
            have hB : (∑ g : G, ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
                f g * Irr.charFun G c g⁻¹) * (Irr.charFun G c g * Irr.charFun G d g⁻¹)) =
                ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
                  (∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun c _ => ?_
              exact (Finset.mul_sum _ _ _).symm
            rw [hB]
    have hexpand : (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        (f - ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) •
          Irr.charFun G c) g * Irr.charFun G d g⁻¹ =
        (Nat.card G : ℂ)⁻¹ * (∑ g : G, f g * Irr.charFun G d g⁻¹) -
          (Nat.card G : ℂ)⁻¹ * (∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
            f g * Irr.charFun G c g⁻¹) *
            (∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹)) := by
      rw [h2, mul_sub]
    have hY : (Nat.card G : ℂ)⁻¹ * (∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
        f g * Irr.charFun G c g⁻¹) *
        (∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹)) =
        ∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
          (if c = d then 1 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hring : (Nat.card G : ℂ)⁻¹ *
          (((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
            (∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹)) =
          ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
            ((Nat.card G : ℂ)⁻¹ * ∑ g : G, Irr.charFun G c g * Irr.charFun G d g⁻¹) := by
        ring
      rw [hring, charInner_orth]
    have h3 : (∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G c g⁻¹) *
        (if c = d then (1:ℂ) else 0)) =
        (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * Irr.charFun G d g⁻¹ := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [hexpand, hY, h3, sub_self]
  have hzero := classfun_eq_zero_of_orth G hD horth
  exact sub_eq_zero.mp hzero

open Classical in
/-- The delta class function at the identity. -/
noncomputable def deltaOne : G → ℂ := fun g => if g = 1 then 1 else 0

omit [Fintype G] in
theorem deltaOne_classfun : IsClassFun G (deltaOne G) := by
  classical
  intro g h
  change (if h * g * h⁻¹ = 1 then (1:ℂ) else 0) = (if g = 1 then 1 else 0)
  by_cases hcon : g = 1
  · subst hcon
    simp
  · rw [ite_eq_right hcon]
    have hne : h * g * h⁻¹ ≠ 1 := by
      intro hh
      apply hcon
      have hxx := congrArg (fun x => h⁻¹ * x * h) hh
      have hgg : h⁻¹ * (h * g * h⁻¹) * h = g := by group
      rw [hgg] at hxx
      simpa using hxx
    rw [ite_eq_right hne]

/-- Inner product of the delta function with a character picks out `χ 1 / |G|`. -/
theorem deltaOne_inner (c : Irr G) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, deltaOne G g * Irr.charFun G c g⁻¹ =
      (Nat.card G : ℂ)⁻¹ * Irr.charFun G c 1 := by
  classical
  have hsum : (∑ g : G, deltaOne G g * Irr.charFun G c g⁻¹) = Irr.charFun G c 1 := by
    calc (∑ g : G, deltaOne G g * Irr.charFun G c g⁻¹)
        = ∑ g : G, (if g = 1 then Irr.charFun G c g⁻¹ else 0) :=
          Finset.sum_congr rfl fun g _ => by
            change (if g = 1 then (1:ℂ) else 0) * _ = _
            by_cases hg : g = 1 <;> simp [hg]
      _ = Irr.charFun G c 1⁻¹ := by
          rw [Finset.sum_ite_eq']
          simp
      _ = Irr.charFun G c 1 := by rw [inv_one]
  rw [hsum]

/-- The regular character vanishes off the identity (column orthogonality). -/
theorem regular_character_vanishes (g : G) (hg : g ≠ 1) :
    ∑ c : Irr G, Irr.charFun G c 1 * Irr.charFun G c g = 0 := by
  classical
  have hexp := classfun_expand G (deltaOne_classfun G)
  have hpt := congrFun hexp g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, deltaOne_inner] at hpt
  have hdelta : deltaOne G g = 0 := ite_eq_right hg
  rw [hdelta] at hpt
  have hfac : (∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * Irr.charFun G c 1) * Irr.charFun G c g) =
      (Nat.card G : ℂ)⁻¹ * ∑ c : Irr G, Irr.charFun G c 1 * Irr.charFun G c g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hfac] at hpt
  have hcard : (Nat.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero (NeZero.ne _)
  exact (mul_eq_zero.mp hpt.symm).resolve_left hcard

/-- The sum of squared degrees equals the group order. -/
theorem sum_deg_sq : ∑ c : Irr G, (Irr.charFun G c 1) ^ 2 = (Fintype.card G : ℂ) := by
  classical
  have hexp := classfun_expand G (deltaOne_classfun G)
  have hpt := congrFun hexp 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, deltaOne_inner] at hpt
  have hdelta : deltaOne G 1 = 1 := ite_eq_left rfl
  rw [hdelta] at hpt
  have hfac : (∑ c : Irr G, ((Nat.card G : ℂ)⁻¹ * Irr.charFun G c 1) * Irr.charFun G c 1) =
      (Nat.card G : ℂ)⁻¹ * ∑ c : Irr G, Irr.charFun G c 1 * Irr.charFun G c 1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hfac] at hpt
  have hcard : (Nat.card G : ℂ) ≠ 0 := NeZero.ne _
  have hS : (∑ c : Irr G, Irr.charFun G c 1 * Irr.charFun G c 1) = (Nat.card G : ℂ) := by
    have h := congrArg ((Nat.card G : ℂ) * ·) hpt
    rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h
    exact h.symm
  simp only [pow_two]
  rw [hS, Nat.card_eq_fintype_card]

end

end BurnsidePaqb
