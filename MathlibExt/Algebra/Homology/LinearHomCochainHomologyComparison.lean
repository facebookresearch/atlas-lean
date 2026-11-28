/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
import MathlibExt.Algebra.Homology.LinearHomCochainComplexQuasiIso

/-!
# Canonical comparison from Hom cochain cohomology to Hom of chain homology

Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For a nonnegative chain complex K and M∈C, put D=Hom_C(K,M).
A cocycle f∈Z^nD is a morphism K_n→M killed by the incoming chain boundary. Its restriction to
Z_nK descends to a morphism H_nK→M. This descent is R-linear and kills cochain boundaries,
giving the canonical map Φ_n:H^nD→Hom_C(H_nK,M) in R-modules with carriers in v.

The comparison commutes with coefficient postcomposition and chain precomposition. If every K_i
and every H_iK is projective in C, then Φ_n is an isomorphism for all n∈ℕ and every M. The
resulting isomorphism has this same canonical restriction-and-descent map as its forward
morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace HomologicalComplex

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For a chain complex K of shape down ℕ, M∈C, n∈ℕ and f∈Z^nD
with D=Hom_C(K,M), let f̄:K_n→M be its underlying cochain. Since f̄ kills the incoming boundary,
restricting to Z_nK gives this morphism d_f:H_nK→M. It is characterized by
π_{K,n}≫d_f=i_{K,n}≫f̄. -/
public noncomputable def linearHomCochainCycleDesc
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    (f : (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K) :
    K.homology n ⟶ M := by
  let D := (linearHomCochainComplexFunctor R C M).obj (op K)
  let f' : K.X n ⟶ M :=
    (D.iCycles n).hom f
  let hmid : (K.sc n).X₂ ⟶ M := by
    with_unfolding_all exact f'
  let hfac : (K.sc n).cycles ⟶ M := (K.sc n).iCycles ≫ hmid
  have hfac_eq : (K.sc n).toCycles ≫ hfac =
      (K.sc n).f ≫ hmid := by
    simpa only [hfac] using
      (ShortComplex.toCycles_i_assoc (S := K.sc n) hmid)
  have hsource : (K.sc n).f ≫ hmid = 0 := by
    have hf := ConcreteCategory.congr_hom ((D.sc n).iCycles_g) f
    have hdual :
        (D.sc n).g.hom ((D.sc n).iCycles.hom f) =
          (K.sc n).f ≫ hmid := by
      with_unfolding_all rfl
    exact hdual.symm.trans hf
  exact (K.sc n).descHomology hfac (hfac_eq.trans hsource)

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K, M, n and a Hom cochain cocycle f∈Z^nHom_C(K,M), let
d_f:H_nK→M be its descended map and f̄:K_n→M the underlying cochain. Then
π_{K,n}≫d_f=i_{K,n}≫f̄. The equality is on the entire chain-cycles object Z_nK. -/
@[reassoc]
public theorem linearHomCochainCycleDesc_fac
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    (f : (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K) :
    K.homologyπ n ≫ linearHomCochainCycleDesc R K M n f =
      K.iCycles n ≫
        (((linearHomCochainComplexFunctor R C M).obj
          (op K)).iCycles n).hom f := by
  unfold linearHomCochainCycleDesc
  with_unfolding_all
    apply ShortComplex.π_descHomology

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K of shape down ℕ, M∈C and n∈ℕ, this R-linear map
ρ_n:Z^nHom_C(K,M)→Hom_C(H_nK,M) sends f to its canonical descent d_f. It uses restriction to
Z_nK and the homology quotient, and both Hom modules have carriers in v. -/
public noncomputable def linearHomCochainCyclesComparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K ⟶
      ModuleCat.of R (K.homology n ⟶ M) :=
  ModuleCat.ofHom
    { toFun := linearHomCochainCycleDesc R K M n
      map_add' := by
        intro f g
        apply (cancel_epi (K.homologyπ n)).1
        rw [linearHomCochainCycleDesc_fac,
          Preadditive.comp_add,
          linearHomCochainCycleDesc_fac,
          linearHomCochainCycleDesc_fac]
        exact (congrArg (fun z => K.iCycles n ≫ z)
          (map_add ((((linearHomCochainComplexFunctor R C M).obj
            (op K)).iCycles n).hom) f g)).trans
          (by apply Preadditive.comp_add)
      map_smul' := by
        intro r f
        apply (cancel_epi (K.homologyπ n)).1
        rw [linearHomCochainCycleDesc_fac,
          Linear.comp_smul,
          linearHomCochainCycleDesc_fac]
        exact (congrArg (fun z => K.iCycles n ≫ z)
          (map_smul ((((linearHomCochainComplexFunctor R C M).obj
            (op K)).iCycles n).hom) r f)).trans
          (by apply Linear.comp_smul) }

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K,M,n and f∈Z^nHom_C(K,M), the comparison ρ_n sends f to
d_f:H_nK→M, the morphism characterized by π_{K,n}≫d_f=i_{K,n}≫f̄. The equality identifies its
underlying R-linear map on every cochain cocycle. -/
@[simp]
public theorem linearHomCochainCyclesComparison_hom_apply
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    (f : (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K) :
    linearHomCochainCycleDesc R K M n f =
      (linearHomCochainCyclesComparison R K M n).hom f :=
  rfl

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K,M,n, let D=Hom_C(K,M) and ρ_n:Z^nD→Hom_C(H_nK,M) be
the cycles comparison. The boundary-to-cycles map of D followed by ρ_n is zero. A cochain
boundary factors through the outgoing chain differential, whose restriction to Z_nK is zero. -/
public theorem linearHomCochain_toCycles_comp_cyclesComparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    (((linearHomCochainComplexFunctor R C M).obj (op K)).sc n).toCycles ≫
        linearHomCochainCyclesComparison R K M n =
      0 := by
  let D := (linearHomCochainComplexFunctor R C M).obj (op K)
  apply ModuleCat.hom_ext
  ext f
  let bcycle : (D.sc n).leftHomologyData.K := by
    with_unfolding_all exact (D.sc n).toCycles.hom f
  change linearHomCochainCycleDesc R K M n bcycle = 0
  apply (cancel_epi (K.homologyπ n)).1
  rw [Limits.comp_zero, linearHomCochainCycleDesc_fac]
  have hf :
      (D.iCycles n).hom
          bcycle =
        (D.sc n).f.hom f := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom ((D.sc n).toCycles_i) f
  let ftail : K.X ((ComplexShape.down ℕ).next n) ⟶ M := by
    with_unfolding_all exact f
  have hD : (D.sc n).f.hom f =
      K.d n ((ComplexShape.down ℕ).next n) ≫ ftail := by
    with_unfolding_all rfl
  rw [hf, hD]
  simpa only [Limits.zero_comp] using
    K.iCycles_d_assoc n ((ComplexShape.down ℕ).next n) ftail

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K of shape down ℕ, M∈C and n∈ℕ, this is the canonical
R-linear map Φ_n:H^nHom_C(K,M)→Hom_C(H_nK,M). It descends the cycles comparison because cochain
boundaries induce the zero homology morphism. On a class represented by cocycle f, Φ_n([f]) is
d_f, characterized by π_{K,n}≫d_f=i_{K,n}≫f̄. -/
public noncomputable def linearHomCochainHomologyComparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj (op K)).homology n ⟶
      ModuleCat.of R (K.homology n ⟶ M) :=
  (((linearHomCochainComplexFunctor R C M).obj (op K)).sc n).descHomology
    (linearHomCochainCyclesComparison R K M n)
    (linearHomCochain_toCycles_comp_cyclesComparison R K M n)

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K,M,n and D=Hom_C(K,M), let ρ_n:Z^nD→Hom_C(H_nK,M) be
restriction and descent from cycles, and Φ_n:H^nD→Hom_C(H_nK,M) the cohomology comparison. Then
π_D^n≫Φ_n=ρ_n. The equality specifies Φ_n on every cocycle representative. -/
@[reassoc (attr := simp)]
public theorem linearHomCochainHomologyπ_comp_comparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj (op K)).homologyπ n ≫
        linearHomCochainHomologyComparison R K M n =
      linearHomCochainCyclesComparison R K M n := by
  apply ShortComplex.π_descHomology

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K of shape down ℕ, a:M→N and n∈ℕ, the comparison maps
satisfy H^n(postcompose(a))≫Φ_{K,N,n}=Φ_{K,M,n}≫postcompose(a). The map on the right acts on
Hom_C(H_nK,M) by d↦d≫a, while the left map acts on Hom cochain cohomology. -/
@[reassoc]
public theorem linearHomCochainHomologyComparison_naturality_coefficient
    (K : ChainComplex C ℕ) {M N : C} (a : M ⟶ N) (n : ℕ) :
    homologyMap
          (((linearHomCochainComplexBifunctor R C).map a).app (op K)) n ≫
        linearHomCochainHomologyComparison R K N n =
      linearHomCochainHomologyComparison R K M n ≫
        ((linearYoneda R C).map a).app (op (K.homology n)) := by
  let Dₘ := (linearHomCochainComplexFunctor R C M).obj (op K)
  let Dₙ := (linearHomCochainComplexFunctor R C N).obj (op K)
  let F : Dₘ ⟶ Dₙ := by
    with_unfolding_all
      exact ((linearHomCochainComplexBifunctor R C).map a).app (op K)
  let cF : (Dₘ.sc n).leftHomologyData.K ⟶
      (Dₙ.sc n).leftHomologyData.K := by
    with_unfolding_all exact cyclesMap F n
  let aH : ModuleCat.of R (K.homology n ⟶ M) ⟶
      ModuleCat.of R (K.homology n ⟶ N) := by
    with_unfolding_all
      exact ((linearYoneda R C).map a).app (op (K.homology n))
  with_unfolding_all
    change homologyMap F n ≫
        linearHomCochainHomologyComparison R K N n =
      linearHomCochainHomologyComparison R K M n ≫ aH
  apply (cancel_epi (Dₘ.homologyπ n)).1
  rw [homologyπ_naturality_assoc,
    linearHomCochainHomologyπ_comp_comparison]
  with_unfolding_all
    change cF ≫ linearHomCochainCyclesComparison R K N n =
      Dₘ.homologyπ n ≫
        linearHomCochainHomologyComparison R K M n ≫
          aH
  rw [linearHomCochainHomologyπ_comp_comparison_assoc]
  apply ModuleCat.hom_ext
  ext f
  apply (cancel_epi (K.homologyπ n)).1
  with_unfolding_all
    change K.homologyπ n ≫
        linearHomCochainCycleDesc R K N n (cF.hom f) =
      K.homologyπ n ≫ (linearHomCochainCycleDesc R K M n f ≫ a)
  rw [linearHomCochainCycleDesc_fac]
  rw [← Category.assoc, linearHomCochainCycleDesc_fac]
  have hf :
      (Dₙ.iCycles n).hom (cF.hom f) =
        (Dₘ.iCycles n).hom f ≫ a := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom (cyclesMap_i F n) f
  rw [hf]
  exact (Category.assoc _ _ _).symm

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For a chain map f:K→L of shape down ℕ, coefficient M and
n∈ℕ, one has H^n(precompose(f))≫Φ_{K,M,n}=Φ_{L,M,n}≫precompose(H_n(f)). Both sides map
H^nHom_C(L,M) to Hom_C(H_nK,M), retaining the contravariant chain direction. -/
@[reassoc]
public theorem linearHomCochainHomologyComparison_naturality_chain
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (M : C) (n : ℕ) :
    homologyMap ((linearHomCochainComplexFunctor R C M).map f.op) n ≫
        linearHomCochainHomologyComparison R K M n =
      linearHomCochainHomologyComparison R L M n ≫
        ModuleCat.ofHom (Linear.leftComp R M (homologyMap f n)) := by
  let Dₖ := (linearHomCochainComplexFunctor R C M).obj (op K)
  let Dₗ := (linearHomCochainComplexFunctor R C M).obj (op L)
  let F := (linearHomCochainComplexFunctor R C M).map f.op
  let cF : (Dₗ.sc n).leftHomologyData.K ⟶
      (Dₖ.sc n).leftHomologyData.K := by
    with_unfolding_all exact cyclesMap F n
  apply (cancel_epi (Dₗ.homologyπ n)).1
  rw [homologyπ_naturality_assoc,
    linearHomCochainHomologyπ_comp_comparison]
  with_unfolding_all
    change cF ≫ linearHomCochainCyclesComparison R K M n =
      Dₗ.homologyπ n ≫
        linearHomCochainHomologyComparison R L M n ≫
          ModuleCat.ofHom (Linear.leftComp R M (homologyMap f n))
  rw [linearHomCochainHomologyπ_comp_comparison_assoc]
  apply ModuleCat.hom_ext
  ext φ
  apply (cancel_epi (K.homologyπ n)).1
  change K.homologyπ n ≫
      linearHomCochainCycleDesc R K M n (cF.hom φ) =
    K.homologyπ n ≫
      (homologyMap f n ≫ linearHomCochainCycleDesc R L M n φ)
  rw [linearHomCochainCycleDesc_fac]
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    linearHomCochainCycleDesc_fac]
  have hφ :
      (Dₖ.iCycles n).hom (cF.hom φ) =
        f.f n ≫ (Dₗ.iCycles n).hom φ := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom (cyclesMap_i F n) φ
  rw [hφ]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ ((Dₗ.iCycles n).hom φ))
      (cyclesMap_i f n).symm)).trans
    (Category.assoc _ _ _)

/-!
# Projective terms and projective homology make the canonical comparison invertible

For a nonnegative chain complex K in an abelian R-linear category, assume every term K_i and
homology object H_iK is projective. The epimorphisms Z_iK→H_iK admit sections, giving a chain
map from the zero-differential homology complex to K which induces the homology identifications.
The projective-complex comparison then identifies their Hom cochain cohomology.

Consequently Φ_n:H^nHom_C(K,M)→Hom_C(H_nK,M) is invertible for every coefficient object M and
every n∈ℕ. The public isomorphism is the one whose forward map is Φ_n, with arbitrary scalar,
object and morphism universes.
-/

private noncomputable def homologyComplex (K : ChainComplex C ℕ) :
    ChainComplex C ℕ where
  X i := K.homology i
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private noncomputable def homologyComplexXIso
    (K : ChainComplex C ℕ) (i : ℕ) :
    (homologyComplex K).X i ≅ K.homology i :=
  Iso.refl _

@[simp]
private lemma homologyComplex_d (K : ChainComplex C ℕ) (i j : ℕ) :
    (homologyComplex K).d i j = 0 :=
  rfl

private noncomputable def homologyCycleSection
    (K : ChainComplex C ℕ) (i : ℕ) [Projective (K.homology i)] :
    K.homology i ⟶ K.cycles i :=
  Projective.factorThru (f := 𝟙 (K.homology i)) (K.homologyπ i)

@[reassoc (attr := simp)]
private theorem homologyCycleSection_comp_homologyπ
    (K : ChainComplex C ℕ) (i : ℕ) [Projective (K.homology i)] :
    homologyCycleSection K i ≫ K.homologyπ i = 𝟙 _ := by
  apply Projective.factorThru_comp

/-- Let C be an abelian category with arbitrary object and morphism universes, K a nonnegative chain
complex, and assume every H_iK is projective. Let H(K) be the chain complex with terms H_iK and
zero differentials. Sections s_i:H_iK→Z_iK of π_i give this chain map H(K)→K with degree-i
component s_i≫i_i. Under the zero-differential homology identifications it induces the identity
on H_iK. -/
private noncomputable def homologyComplexTo
    (K : ChainComplex C ℕ) [hK : ∀ i, Projective (K.homology i)] :
    homologyComplex K ⟶ K where
  f i := by
    let _ : Projective (K.homology i) := hK i
    exact (homologyComplexXIso K i).hom ≫
      homologyCycleSection K i ≫ K.iCycles i
  comm' i j _ := by
    rw [homologyComplex_d, zero_comp, Category.assoc, Category.assoc,
      iCycles_d, comp_zero, comp_zero]

@[simp]
private theorem homologyComplexTo_f
    (K : ChainComplex C ℕ) [hK : ∀ i, Projective (K.homology i)] (i : ℕ) :
    (homologyComplexTo K).f i =
      (homologyComplexXIso K i).hom ≫
        homologyCycleSection K i ≫ K.iCycles i := by
  let _ : Projective (K.homology i) := hK i
  rfl

set_option linter.style.haveILetI false in
private theorem homologyComplexTo_quasiIso
    (K : ChainComplex C ℕ) [hK : ∀ i, Projective (K.homology i)] :
    QuasiIso (homologyComplexTo K) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let _ : Projective (K.homology i) := hK i
  let hICycles : IsIso ((homologyComplex K).iCycles i) :=
    ShortComplex.isIso_iCycles ((homologyComplex K).sc i) (by
      simp only [shortComplexFunctor_obj_g, homologyComplex_d])
  letI : IsIso ((homologyComplex K).iCycles i) := hICycles
  let hHomologyπ : IsIso ((homologyComplex K).homologyπ i) :=
    ShortComplex.isIso_homologyπ ((homologyComplex K).sc i) (by
      simp only [shortComplexFunctor_obj_f, homologyComplex_d])
  letI : IsIso ((homologyComplex K).homologyπ i) := hHomologyπ
  have hcycles :
      cyclesMap (homologyComplexTo K) i =
        (homologyComplex K).iCycles i ≫
          (homologyComplexXIso K i).hom ≫
            homologyCycleSection K i := by
    apply (cancel_mono (K.iCycles i)).1
    rw [cyclesMap_i, homologyComplexTo_f]
    simp only [Category.assoc]
  have h :
      (homologyComplex K).homologyπ i ≫
          homologyMap (homologyComplexTo K) i =
        (homologyComplex K).iCycles i ≫
          (homologyComplexXIso K i).hom := by
    simp only [homologyπ_naturality, hcycles, Category.assoc,
      homologyCycleSection_comp_homologyπ, Category.comp_id]
  let htarget : IsIso ((homologyComplex K).iCycles i ≫
      (homologyComplexXIso K i).hom) := by infer_instance
  let hcomp : IsIso ((homologyComplex K).homologyπ i ≫
      homologyMap (homologyComplexTo K) i) := h ▸ htarget
  letI : IsIso ((homologyComplex K).homologyπ i ≫
      homologyMap (homologyComplexTo K) i) := hcomp
  exact IsIso.of_isIso_comp_left ((homologyComplex K).homologyπ i)
    (homologyMap (homologyComplexTo K) i)

private theorem homologyπ_comp_homologyIsoOfZeros_hom
    {A : Type u'} [Category.{v'} A] [Abelian A]
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (i : ι)
    (hf : (K.sc i).f = 0) (hg : (K.sc i).g = 0) :
    K.homologyπ i ≫
        ((ShortComplex.HomologyData.ofZeros (K.sc i) hf hg).left.homologyIso).hom =
      K.iCycles i := by
  let h := (ShortComplex.HomologyData.ofZeros (K.sc i) hf hg).left
  change (K.sc i).homologyπ ≫ h.homologyIso.hom = (K.sc i).iCycles
  rw [h.homologyπ_comp_homologyIso_hom, ← h.cyclesIso_hom_comp_i]
  rfl

private noncomputable def homologyComplexHomologyIsoX
    (K : ChainComplex C ℕ) (n : ℕ) :
    (homologyComplex K).homology n ≅ (homologyComplex K).X n :=
  (ShortComplex.HomologyData.ofZeros ((homologyComplex K).sc n)
    (by
      simp only [shortComplexFunctor_obj_f, homologyComplex_d])
    (by
      simp only [shortComplexFunctor_obj_g, homologyComplex_d])).left.homologyIso

private lemma linearHomHomologyComplex_d
    (K : ChainComplex C ℕ) (M : C) (i j : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj
      (op (homologyComplex K))).d i j = 0 := by
  change ((linearYoneda R C).obj M).map
      ((homologyComplex K).d j i).op = 0
  rw [homologyComplex_d]
  simp only [op_zero, Functor.map_zero]

private noncomputable def linearHomHomologyComplexHomologyIsoX
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj
        (op (homologyComplex K))).homology n ≅
      ((linearHomCochainComplexFunctor R C M).obj
        (op (homologyComplex K))).X n :=
  (ShortComplex.HomologyData.ofZeros
    (((linearHomCochainComplexFunctor R C M).obj
      (op (homologyComplex K))).sc n)
    (by
      simp only [shortComplexFunctor_obj_f, linearHomHomologyComplex_d])
    (by
      simp only [shortComplexFunctor_obj_g, linearHomHomologyComplex_d])).left.homologyIso

private noncomputable def homologyComplexComparisonIso
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj
        (op (homologyComplex K))).homology n ≅
      ModuleCat.of R ((homologyComplex K).homology n ⟶ M) :=
  linearHomHomologyComplexHomologyIsoX R K M n ≪≫
    ((linearYoneda R C).obj M).mapIso (homologyComplexHomologyIsoX K n).op

private theorem linearHomCochainHomologyComparison_homologyComplex
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    linearHomCochainHomologyComparison R (homologyComplex K) M n =
      (homologyComplexComparisonIso R K M n).hom := by
  let H := homologyComplex K
  let D := (linearHomCochainComplexFunctor R C M).obj (op H)
  let eH := homologyComplexHomologyIsoX K n
  let eD := linearHomHomologyComplexHomologyIsoX R K M n
  let iD : (D.sc n).leftHomologyData.K ⟶ D.X n := by
    with_unfolding_all exact D.iCycles n
  let p : D.X n ⟶ ModuleCat.of R (H.homology n ⟶ M) := by
    with_unfolding_all exact (((linearYoneda R C).obj M).mapIso eH.op).hom
  apply (cancel_epi (D.homologyπ n)).1
  rw [linearHomCochainHomologyπ_comp_comparison]
  have hDπ : D.homologyπ n ≫ eD.hom = iD := by
    with_unfolding_all
      apply homologyπ_comp_homologyIsoOfZeros_hom
  with_unfolding_all
    change linearHomCochainCyclesComparison R H M n =
      D.homologyπ n ≫ eD.hom ≫ p
  have hDπp : D.homologyπ n ≫ eD.hom ≫ p = iD ≫ p := by
    rw [← Category.assoc, hDπ]
    rfl
  rw [hDπp]
  apply ModuleCat.hom_ext
  ext f
  apply (cancel_epi (H.homologyπ n)).1
  change H.homologyπ n ≫ linearHomCochainCycleDesc R H M n f =
    H.homologyπ n ≫ p.hom (iD.hom f)
  rw [linearHomCochainCycleDesc_fac]
  let φ : H.X n ⟶ M :=
    (D.iCycles n).hom f
  have hp : p.hom (iD.hom f) = eH.hom ≫ φ := by
    with_unfolding_all rfl
  have hHπ : H.homologyπ n ≫ eH.hom = H.iCycles n := by
    dsimp only [H, eH, homologyComplexHomologyIsoX]
    apply homologyπ_comp_homologyIsoOfZeros_hom
  change H.iCycles n ≫ φ = H.homologyπ n ≫ p.hom (iD.hom f)
  rw [hp, ← Category.assoc, hHπ]

private theorem linearHomCochainHomologyComparison_homologyComplex_isIso
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    IsIso (linearHomCochainHomologyComparison R
      (homologyComplex K) M n) := by
  rw [linearHomCochainHomologyComparison_homologyComplex]
  infer_instance

set_option linter.style.haveILetI false in
/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K of shape down ℕ, assume K_i and H_iK are projective
objects of C for every i∈ℕ. For arbitrary M∈C and n∈ℕ, the canonical map
Φ_n:H^nHom_C(K,M)→Hom_C(H_nK,M) is an isomorphism. Both complete projectivity families are
hypotheses, and the coefficient M is unrestricted. -/
public theorem linearHomCochainHomologyComparison_isIso_of_projective_terms_and_homology
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    [hK : ∀ i, Projective (K.X i)]
    [hH : ∀ i, Projective (K.homology i)] :
    IsIso (linearHomCochainHomologyComparison R K M n) := by
  let H := homologyComplex K
  let f := homologyComplexTo K
  let g := (linearHomCochainComplexFunctor R C M).map f.op
  let cH := linearHomCochainHomologyComparison R H M n
  let cK := linearHomCochainHomologyComparison R K M n
  letI : ∀ i, Projective (H.X i) := fun i ↦ hH i
  letI : QuasiIso f := homologyComplexTo_quasiIso K
  letI : QuasiIso g :=
    linearHomCochainComplexFunctor_map_quasiIso_of_projective R f M
  letI : IsIso (homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).mp
      (inferInstance : QuasiIsoAt f n)
  letI : IsIso (homologyMap g n) :=
    (quasiIsoAt_iff_isIso_homologyMap g n).mp
      (inferInstance : QuasiIsoAt g n)
  let ef : H.homology n ≅ K.homology n := asIso (homologyMap f n)
  let pIso : ModuleCat.of R (K.homology n ⟶ M) ≅
      ModuleCat.of R (H.homology n ⟶ M) :=
    ((linearYoneda R C).obj M).mapIso ef.op
  let hcH : IsIso cH :=
    linearHomCochainHomologyComparison_homologyComplex_isIso R K M n
  letI : IsIso cH := hcH
  have hnat := linearHomCochainHomologyComparison_naturality_chain R f M n
  have hnat' : homologyMap g n ≫ cH = cK ≫ pIso.hom := by
    exact hnat
  let hleft : IsIso (homologyMap g n ≫ cH) := by infer_instance
  let hright : IsIso (cK ≫ pIso.hom) := hnat' ▸ hleft
  letI : IsIso (cK ≫ pIso.hom) := hright
  exact IsIso.of_isIso_comp_right cK pIso.hom

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For a chain complex K with K_i and H_iK projective for every
i, M∈C and n∈ℕ, this is the canonical isomorphism H^nHom_C(K,M)≅Hom_C(H_nK,M). Its forward map
is Φ_n, sending a cochain cocycle class to the morphism it induces on chain homology. -/
public noncomputable def linearHomCochainHomologyIsoOfProjectiveTermsAndHomology
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    ((linearHomCochainComplexFunctor R C M).obj (op K)).homology n ≅
      ModuleCat.of R (K.homology n ⟶ M) := by
  letI := linearHomCochainHomologyComparison_isIso_of_projective_terms_and_homology
    R K M n
  exact asIso (linearHomCochainHomologyComparison R K M n)

/-- Let R be a ring in universe w and C an abelian R-linear category with independent object
universe u and morphism universe v. For K of shape down ℕ with every K_i and H_iK projective,
coefficient M and n∈ℕ, the forward morphism of H^nHom_C(K,M)≅Hom_C(H_nK,M) equals Φ_n. The
equality identifies the isomorphism through the given cochain restriction-and-descent
comparison. -/
@[simp]
public theorem linearHomCochainHomologyIsoOfProjectiveTermsAndHomology_hom
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    (linearHomCochainHomologyIsoOfProjectiveTermsAndHomology R K M n).hom =
      linearHomCochainHomologyComparison R K M n :=
  rfl

end HomologicalComplex

end
