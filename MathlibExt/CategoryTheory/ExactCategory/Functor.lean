/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import MathlibExt.CategoryTheory.ExactCategory.Basic
import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag
import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Exact functors between Quillen exact categories

Let `C`, `D` be additive categories endowed with chosen exact structures.
An additive functor `F : C → D` is exact when it preserves every
admissible kernel–cokernel sequence. Reflection of admissible exactness
is the converse condition on mapped short complexes. Exact functors
preserve the stated admissible pullback and pushout squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ExactCategory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For additive categories `C`, `D` with Quillen exact structures, an
additive functor `F : C → D` is exact when the image of each admissible
exact short complex of `C` is admissible exact in `D`. -/
class Functor.IsExact (F : C ⥤ D) [F.Additive] : Prop where
  map_admissibleExact (S : ShortComplex C) :
    IsAdmissibleExact S → IsAdmissibleExact (S.map F)

lemma Functor.map_admissibleExact (F : C ⥤ D) [F.Additive] [F.IsExact] (S : ShortComplex C)
    (hS : IsAdmissibleExact S) : IsAdmissibleExact (S.map F) :=
  Functor.IsExact.map_admissibleExact S hS

/-- Let `F : C → D` be an additive exact functor between additive exact
categories. If a pullback in `C` has target legs an admissible mono
`i : X → Z` and an admissible epi `p : Y → Z`, the square obtained
by applying `F` is a pullback in `D`. -/
lemma Functor.map_isPullback_of_isAdmissibleMono_of_isAdmissibleEpi
    (F : C ⥤ D) [F.Additive] [F.IsExact]
    {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    {i : X ⟶ Z} {p : Y ⟶ Z} (hpb : IsPullback fst snd i p)
    (hi : IsAdmissibleMono i) (hp : IsAdmissibleEpi p) :
    IsPullback (F.map fst) (F.map snd) (F.map i) (F.map p) := by
  have hMono_i : Mono i := hi.mono
  obtain ⟨Wq, q, w_iq, hS_i⟩ := hi
  have hq : IsAdmissibleEpi q := isAdmissibleEpi_g hS_i
  have hpq : IsAdmissibleEpi (p ≫ q) :=
    admissibleEpi_comp.comp_mem _ _ hp hq
  obtain ⟨K, j, w_j, hS_j⟩ := hpq
  have w_snd : snd ≫ (p ≫ q) = 0 := by
    calc snd ≫ (p ≫ q) = (snd ≫ p) ≫ q := by rw [Category.assoc]
      _ = (fst ≫ i) ≫ q := by rw [hpb.w]
      _ = fst ≫ (i ≫ q) := by rw [Category.assoc]
      _ = fst ≫ 0 := by rw [w_iq]
      _ = 0 := by simp
  have hKernel_i : IsLimit (KernelFork.ofι i w_iq) :=
    isLimit_kernelFork_of_isAdmissibleExact hS_i
  have hKernel_snd_source : IsLimit (KernelFork.ofι snd w_snd) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W'} g' hg' => ?_)
      (fun {W'} g' hg' => ?_) (fun {W'} g' hg' m hm => ?_)
    · have h₁ : (g' ≫ p) ≫ q = 0 := by
        calc (g' ≫ p) ≫ q = g' ≫ (p ≫ q) := by rw [Category.assoc]
          _ = 0 := hg'
      let s' : KernelFork q := KernelFork.ofι (g' ≫ p) h₁
      let u : W' ⟶ X := hKernel_i.lift s'
      have hu : u ≫ i = g' ≫ p := by
        have hfac := hKernel_i.fac s' WalkingParallelPair.zero
        simpa [s', KernelFork.ofι] using hfac
      exact hpb.lift u g' hu
    · have h₁ : (g' ≫ p) ≫ q = 0 := by
        calc (g' ≫ p) ≫ q = g' ≫ (p ≫ q) := by rw [Category.assoc]
          _ = 0 := hg'
      let s' : KernelFork q := KernelFork.ofι (g' ≫ p) h₁
      let u : W' ⟶ X := hKernel_i.lift s'
      have hu : u ≫ i = g' ≫ p := by
        have hfac := hKernel_i.fac s' WalkingParallelPair.zero
        simpa [s', KernelFork.ofι] using hfac
      change (hpb.lift u g' hu) ≫ snd = g'
      simp [hpb.lift_snd]
    · have h₁ : (g' ≫ p) ≫ q = 0 := by
        calc (g' ≫ p) ≫ q = g' ≫ (p ≫ q) := by rw [Category.assoc]
          _ = 0 := hg'
      let s' : KernelFork q := KernelFork.ofι (g' ≫ p) h₁
      let u : W' ⟶ X := hKernel_i.lift s'
      have hu : u ≫ i = g' ≫ p := by
        have hfac := hKernel_i.fac s' WalkingParallelPair.zero
        simpa [s', KernelFork.ofι] using hfac
      let v : W' ⟶ P := hpb.lift u g' hu
      have hv_fst : v ≫ fst = u := by simp [v]
      have hv_snd : v ≫ snd = g' := by simp [v]
      have hm_snd : m ≫ snd = v ≫ snd := by rw [hm, hv_snd]
      have hm_fst : m ≫ fst = v ≫ fst := by
        have h_eq : (m ≫ fst) ≫ i = (v ≫ fst) ≫ i := by
          calc (m ≫ fst) ≫ i = m ≫ (fst ≫ i) := by rw [Category.assoc]
            _ = m ≫ (snd ≫ p) := by rw [hpb.w]
            _ = (m ≫ snd) ≫ p := by rw [Category.assoc]
            _ = g' ≫ p := by rw [hm]
            _ = u ≫ i := hu.symm
            _ = (v ≫ fst) ≫ i := by rw [hv_fst]
        exact (cancel_mono i).mp h_eq
      exact hpb.hom_ext hm_fst hm_snd
  have hKernel_j : IsLimit (KernelFork.ofι j w_j) :=
    isLimit_kernelFork_of_isAdmissibleExact hS_j
  have hS_snd_source : IsAdmissibleExact (ShortComplex.mk snd (p ≫ q) w_snd) := by
    let e : P ≅ K := IsLimit.conePointUniqueUpToIso hKernel_snd_source hKernel_j
    have h_comm₁ : e.hom ≫ j = snd := by
      have h := IsLimit.conePointUniqueUpToIso_hom_comp
        hKernel_snd_source hKernel_j WalkingParallelPair.zero
      simpa [KernelFork.ofι] using h
    have h_comm₁' : e.hom ≫ j = snd ≫ (Iso.refl _).hom := by
      simp [h_comm₁]
    have h_comm₂' : (Iso.refl _).hom ≫ (p ≫ q) =
        (p ≫ q) ≫ (Iso.refl _).hom := by simp
    let S_snd : ShortComplex C := ShortComplex.mk snd (p ≫ q) w_snd
    let S_j : ShortComplex C := ShortComplex.mk j (p ≫ q) w_j
    have h_iso : S_snd ≅ S_j :=
      ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) h_comm₁' h_comm₂'
    exact isAdmissibleExact_of_iso h_iso.symm hS_j
  have hAdm_Fi : IsAdmissibleMono (F.map i) :=
    ⟨_, _, _, F.map_admissibleExact _ hS_i⟩
  have hMono_Fi : Mono (F.map i) := hAdm_Fi.mono
  have hZero_mapped : F.map snd ≫ F.map (p ≫ q) = 0 := by
    rw [← F.map_comp, w_snd, F.map_zero]
  have hMappedExact : IsAdmissibleExact
      (ShortComplex.mk (F.map snd) (F.map (p ≫ q)) hZero_mapped) :=
    F.map_admissibleExact _ hS_snd_source
  have hAdm_Fsnd : IsAdmissibleMono (F.map snd) :=
    ⟨_, _, _, hMappedExact⟩
  have hMono_Fsnd : Mono (F.map snd) := hAdm_Fsnd.mono
  have hKernel_mapped : IsLimit
      (KernelFork.ofι (F.map snd) hZero_mapped) :=
    isLimit_kernelFork_of_isAdmissibleExact hMappedExact
  refine IsPullback.mk' ?_ ?_ ?_
  · calc F.map fst ≫ F.map i = F.map (fst ≫ i) := by rw [F.map_comp]
      _ = F.map (snd ≫ p) := by rw [hpb.w]
      _ = F.map snd ≫ F.map p := by rw [F.map_comp]
  · intro T φ φ' _ hψ
    exact (cancel_mono (F.map snd)).mp (hψ.trans rfl)
  · intro T a b hcone
    have hb0 : b ≫ F.map (p ≫ q) = 0 := by
      calc b ≫ F.map (p ≫ q) = b ≫ (F.map p ≫ F.map q) := by rw [F.map_comp]
        _ = (b ≫ F.map p) ≫ F.map q := by rw [Category.assoc]
        _ = (a ≫ F.map i) ≫ F.map q := by rw [← hcone]
        _ = a ≫ (F.map i ≫ F.map q) := by rw [Category.assoc]
        _ = a ≫ F.map (i ≫ q) := by rw [F.map_comp]
        _ = a ≫ F.map 0 := by rw [w_iq]
        _ = 0 := by simp
    let s_b : KernelFork (F.map (p ≫ q)) := KernelFork.ofι b hb0
    let l : T ⟶ F.obj P := hKernel_mapped.lift s_b
    have hl_snd : l ≫ F.map snd = b := by
      have hfac := hKernel_mapped.fac s_b WalkingParallelPair.zero
      simpa [s_b, KernelFork.ofι] using hfac
    have hl_fst : l ≫ F.map fst = a := by
      have h_eq : (l ≫ F.map fst) ≫ F.map i = a ≫ F.map i := by
        calc (l ≫ F.map fst) ≫ F.map i = l ≫ (F.map fst ≫ F.map i) := by
              rw [Category.assoc]
          _ = l ≫ F.map (fst ≫ i) := by rw [F.map_comp]
          _ = l ≫ F.map (snd ≫ p) := by rw [hpb.w]
          _ = l ≫ (F.map snd ≫ F.map p) := by rw [F.map_comp]
          _ = (l ≫ F.map snd) ≫ F.map p := by rw [Category.assoc]
          _ = b ≫ F.map p := by rw [hl_snd]
          _ = a ≫ F.map i := by rw [← hcone]
      exact (cancel_mono (F.map i)).mp h_eq
    exact ⟨l, hl_fst, hl_snd⟩

/-- Let `F : C → D` be an additive exact functor between additive exact
categories. If a pushout in `C` has source legs an admissible epi
`p : X → Y` and an admissible mono `i : X → Z`, the square obtained
by applying `F` is a pushout in `D`. -/
lemma Functor.map_isPushout_of_isAdmissibleEpi_of_isAdmissibleMono
    (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y Z P : C} {p : X ⟶ Y} {i : X ⟶ Z}
    {inl : Y ⟶ P} {inr : Z ⟶ P}
    (hpo : IsPushout p i inl inr)
    (hp : IsAdmissibleEpi p) (hi : IsAdmissibleMono i) :
    IsPushout (F.map p) (F.map i) (F.map inl) (F.map inr) := by
  obtain ⟨K, j, w_jp, hS_p⟩ := hp
  obtain ⟨Q, q, w_iq, hS_i⟩ := hi
  have w_inr : (j ≫ i) ≫ inr = 0 := by
    rw [Category.assoc, ← hpo.w, ← Category.assoc, w_jp, zero_comp]
  have hS_inr :
      IsAdmissibleExact (ShortComplex.mk (j ≫ i) inr w_inr) := by
    simpa only using
      isAdmissibleExact_comp_pushout
        j p i q inl inr w_jp w_iq hS_p hS_i hpo
  have hAdm_Fp : IsAdmissibleEpi (F.map p) :=
    ⟨_, _, _, F.map_admissibleExact _ hS_p⟩
  have hEpi_Fp : Epi (F.map p) := hAdm_Fp.epi
  have w_map_inr : F.map (j ≫ i) ≫ F.map inr = 0 := by
    rw [← F.map_comp, w_inr, F.map_zero]
  have hS_map_inr : IsAdmissibleExact
      (ShortComplex.mk (F.map (j ≫ i)) (F.map inr) w_map_inr) :=
    F.map_admissibleExact _ hS_inr
  have hAdm_Finr : IsAdmissibleEpi (F.map inr) :=
    ⟨_, _, _, hS_map_inr⟩
  have hEpi_Finr : Epi (F.map inr) := hAdm_Finr.epi
  have hCoker_map_inr : IsColimit
      (CokernelCofork.ofπ (F.map inr) w_map_inr) :=
    isColimit_cokernelCofork_of_isAdmissibleExact hS_map_inr
  have w_map : F.map p ≫ F.map inl = F.map i ≫ F.map inr := by
    calc
      F.map p ≫ F.map inl = F.map (p ≫ inl) := by rw [F.map_comp]
      _ = F.map (i ≫ inr) := by rw [hpo.w]
      _ = F.map i ≫ F.map inr := by rw [F.map_comp]
  refine IsPushout.mk' w_map ?_ ?_
  · intro T φ φ' _ h_inr
    exact (cancel_epi (F.map inr)).mp h_inr
  · intro T a b hcone
    have hb0 : F.map (j ≫ i) ≫ b = 0 := by
      calc
        F.map (j ≫ i) ≫ b = (F.map j ≫ F.map i) ≫ b := by
          rw [F.map_comp]
        _ = F.map j ≫ (F.map i ≫ b) := Category.assoc _ _ _
        _ = F.map j ≫ (F.map p ≫ a) := by rw [← hcone]
        _ = (F.map j ≫ F.map p) ≫ a := (Category.assoc _ _ _).symm
        _ = F.map (j ≫ p) ≫ a := by rw [F.map_comp]
        _ = F.map 0 ≫ a := by rw [w_jp]
        _ = 0 := by simp
    let s_b : CokernelCofork (F.map (j ≫ i)) :=
      CokernelCofork.ofπ b hb0
    let l : F.obj P ⟶ T := hCoker_map_inr.desc s_b
    have hl_inr : F.map inr ≫ l = b := by
      change F.map inr ≫ hCoker_map_inr.desc
        (CokernelCofork.ofπ b hb0) = b
      exact Cofork.IsColimit.π_desc hCoker_map_inr
    have hl_inl : F.map inl ≫ l = a := by
      apply (cancel_epi (F.map p)).mp
      calc
        F.map p ≫ (F.map inl ≫ l) = (F.map p ≫ F.map inl) ≫ l :=
          (Category.assoc _ _ _).symm
        _ = (F.map i ≫ F.map inr) ≫ l := by rw [w_map]
        _ = F.map i ≫ (F.map inr ≫ l) := Category.assoc _ _ _
        _ = F.map i ≫ b := by rw [hl_inr]
        _ = F.map p ≫ a := hcone.symm
    exact ⟨l, hl_inl, hl_inr⟩

/-- Let `F : C → D` be an additive exact functor between additive exact
categories. Every pushout along an admissible monomorphism
`i : X → Y`, with arbitrary other source leg `X → X′`, is carried
to a pushout in `D`. -/
lemma Functor.map_isPushout_of_isAdmissibleMono
    (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y X' P : C} {i : X ⟶ Y} {f : X ⟶ X'}
    {inl : X' ⟶ P} {inr : Y ⟶ P}
    (hpo : IsPushout f i inl inr) (hi : IsAdmissibleMono i) :
    IsPushout (F.map f) (F.map i) (F.map inl) (F.map inr) := by
  obtain ⟨Q, q, wiq, hS⟩ := hi
  let m : P ⟶ Q :=
    pushoutQuotientMap f i q inl inr wiq hpo
  let wm : inl ≫ m = 0 :=
    pushoutQuotientMap_x f i q inl inr wiq hpo
  let S : ShortComplex C := ShortComplex.mk i q wiq
  let T : ShortComplex C := ShortComplex.mk inl m wm
  have hT : IsAdmissibleExact T := by
    simpa only [T, m, wm] using
      isAdmissibleExact_pushoutQuotientMap
        f i q inl inr wiq hS hpo
  let φ : S ⟶ T :=
    ShortComplex.homMk f inr (𝟙 Q) hpo.w (by
      change inr ≫ m = q ≫ 𝟙 Q
      rw [Category.comp_id]
      exact pushoutQuotientMap_y f i q inl inr wiq hpo)
  have hFS : IsAdmissibleExact (S.map F) :=
    F.map_admissibleExact S (by simpa only [S] using hS)
  have hFT : IsAdmissibleExact (T.map F) :=
    F.map_admissibleExact T hT
  have hIsoRight : IsIso ((F.mapShortComplex).map φ).τ₃ := by
    change IsIso (F.map (𝟙 Q))
    infer_instance
  let _ : IsIso ((F.mapShortComplex).map φ).τ₃ := hIsoRight
  have hMapped :=
    isPushout_f_of_isAdmissibleExact_of_isIso_right
      ((F.mapShortComplex).map φ) hFS hFT
  change IsPushout (F.map i) (F.map f) (F.map inr) (F.map inl) at hMapped
  exact hMapped.flip

/-- For additive categories `C`, `D` with chosen exact structures and an
additive functor `F : C → D`, reflection of admissible exactness means:
if the mapped short complex `F(S)` is admissible exact in `D`, then
`S` is admissible exact in `C`. -/
class Functor.ReflectsAdmissibleExact (F : C ⥤ D) [F.Additive] : Prop where
  reflects_admissibleExact (S : ShortComplex C) :
    IsAdmissibleExact (S.map F) → IsAdmissibleExact S

lemma Functor.reflects_admissibleExact (F : C ⥤ D) [F.Additive]
    [F.ReflectsAdmissibleExact] (S : ShortComplex C)
    (hS : IsAdmissibleExact (S.map F)) : IsAdmissibleExact S :=
  Functor.ReflectsAdmissibleExact.reflects_admissibleExact S hS

instance : (𝟭 C).IsExact where
  map_admissibleExact _ hS := hS

instance (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (F ⋙ G).IsExact where
  map_admissibleExact S hS := G.map_admissibleExact _ (F.map_admissibleExact S hS)

end CategoryTheory
