/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingDifferential
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Connecting morphisms and graded cochain pairings

For a fixed cochain complex and two short exact cochain sequences, suppose three graded
pairings commute with the first and second sequence arrows. Pairing on homology is then
compatible with the connecting morphisms.

A connecting map in the right input has the Koszul factor `(-1)^p`, where `p` is the left-
input degree. A connecting map in the left input has coefficient one. Both identities retain
the homology degree transport to `p + q + 1` and the explicit short exactness of the two
sequences.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.CochainGradedPairing

universe u

variable (R : Type u) [CommRing R]

private lemma moduleHom_comp_apply {A B C : ModuleCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) :=
  rfl

@[simp]
private lemma moduleTensorHom_tmul {A B C D : ModuleCat.{u} R}
    (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
    (f ⊗ₘ g).hom (x ⊗ₜ[R] y) = f.hom x ⊗ₜ[R] g.hom y :=
  rfl

@[simp]
private lemma moduleHom_zsmul_apply {A B : ModuleCat.{u} R}
    (n : ℤ) (f : A ⟶ B) (x : A) :
    (n • f).hom x = n • f.hom x :=
  rfl

private theorem right_preimage_eq_d
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (P₁ : CochainGradedPairing K S.X₁ T.X₁)
    (P₂ : CochainGradedPairing K S.X₂ T.X₂)
    (hpair_f : ∀ p q, P₁.pair p q ≫ T.f.f (p + q) =
      (𝟙 (K.X p) ⊗ₘ S.f.f q) ≫ P₂.pair p q)
    (p q : ℕ) (x : K.cycles p) (y : S.X₂.X q)
    (a : S.X₁.X (q + 1))
    (ha : (S.f.f (q + 1)).hom a =
      (S.X₂.d q (q + 1)).hom y) :
    (T.f.f (p + q + 1)).hom
        (((-1 : ℤ) ^ p) •
          (T.X₁.XIsoOfEq
            (show p + (q + 1) = p + q + 1 by omega)).hom.hom
            ((P₁.pair p (q + 1)).hom
              ((K.iCycles p).hom x ⊗ₜ[R] a))) =
      (T.X₂.d (p + q) (p + q + 1)).hom
        ((P₂.pair p q).hom ((K.iCycles p).hom x ⊗ₜ[R] y)) := by
  rw [P₂.pair_d_right_of_cycle R p q x y]
  rw [map_zsmul]
  congr 1
  let e : p + (q + 1) = p + q + 1 := by omega
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.XIsoOfEq_hom_naturality T.f e)
    ((P₁.pair p (q + 1)).hom ((K.iCycles p).hom x ⊗ₜ[R] a))
  symm at hnat
  have hnat' :
      (T.f.f (p + q + 1)).hom
          ((T.X₁.XIsoOfEq e).hom.hom
            ((P₁.pair p (q + 1)).hom
              ((K.iCycles p).hom x ⊗ₜ[R] a))) =
        (T.X₂.XIsoOfEq e).hom.hom
          ((T.f.f (p + (q + 1))).hom
            ((P₁.pair p (q + 1)).hom
              ((K.iCycles p).hom x ⊗ₜ[R] a))) := by
    simpa only [moduleHom_comp_apply] using hnat
  rw [hnat']
  have hcompat := ConcreteCategory.congr_hom (hpair_f p (q + 1))
    ((K.iCycles p).hom x ⊗ₜ[R] a)
  simp only [moduleHom_comp_apply, moduleTensorHom_tmul] at hcompat
  rw [hcompat, ha]
  simp

private theorem cyclesMk_iCycles
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (x : K.cycles n) :
    K.cyclesMk ((K.iCycles n).hom x) (n + 1) (CochainComplex.next ℕ n) (by
      change (K.d n (n + 1)).hom ((K.iCycles n).hom x) = 0
      exact ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) x) = x := by
  apply (ModuleCat.mono_iff_injective (f := K.iCycles n)).mp inferInstance
  change ((forget₂ (ModuleCat R) Ab).map (K.iCycles n))
      (K.cyclesMk ((K.iCycles n).hom x) (n + 1) (CochainComplex.next ℕ n) _) =
    ((forget₂ (ModuleCat R) Ab).map (K.iCycles n)) x
  rw [HomologicalComplex.i_cyclesMk]
  rfl

private theorem delta_apply_cycles
    {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (n : ℕ)
    (z : S.X₃.cycles n) (y : S.X₂.X n)
    (hy : (S.g.f n).hom y = (S.X₃.iCycles n).hom z)
    (x : S.X₁.X (n + 1))
    (hx : (S.f.f (n + 1)).hom x = (S.X₂.d n (n + 1)).hom y) :
    (hS.δ n (n + 1) rfl).hom ((S.X₃.homologyπ n).hom z) =
      (S.X₁.homologyπ (n + 1)).hom
        (S.X₁.cyclesMk x (n + 2) (CochainComplex.next ℕ (n + 1))
          (hS.d_eq_zero_of_f_eq_d_apply n (n + 1) y x hx (n + 2))) := by
  have h := hS.δ_apply n (n + 1) rfl
    ((S.X₃.iCycles n).hom z)
    (by
      change (S.X₃.d n (n + 1)).hom ((S.X₃.iCycles n).hom z) = 0
      exact ConcreteCategory.congr_hom (S.X₃.iCycles_d n (n + 1)) z)
    y hy x hx (n + 2) (CochainComplex.next ℕ (n + 1))
  rw [cyclesMk_iCycles R S.X₃ n z] at h
  exact h

private theorem pairHomology_delta_right_apply_cycles
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (P₁ : CochainGradedPairing K S.X₁ T.X₁)
    (P₂ : CochainGradedPairing K S.X₂ T.X₂)
    (P₃ : CochainGradedPairing K S.X₃ T.X₃)
    (hpair_f : ∀ p q, P₁.pair p q ≫ T.f.f (p + q) =
      (𝟙 (K.X p) ⊗ₘ S.f.f q) ≫ P₂.pair p q)
    (hpair_g : ∀ p q, P₂.pair p q ≫ T.g.f (p + q) =
      (𝟙 (K.X p) ⊗ₘ S.g.f q) ≫ P₃.pair p q)
    (p q : ℕ) (x : K.cycles p) (z : S.X₃.cycles q) :
    (T.X₁.homologyIsoOfEq
        (show p + (q + 1) = p + q + 1 by omega)).hom.hom
      ((P₁.pairHomology p (q + 1)).hom
        ((K.homologyπ p).hom x ⊗ₜ[R]
          (hS.δ q (q + 1) rfl).hom ((S.X₃.homologyπ q).hom z))) =
      ((-1 : ℤ) ^ p) •
        (hT.δ (p + q) (p + q + 1) rfl).hom
          ((P₃.pairHomology p q).hom
            ((K.homologyπ p).hom x ⊗ₜ[R]
              (S.X₃.homologyπ q).hom z)) := by
  have hSq : (S.map
      (HomologicalComplex.eval (ModuleCat.{u} R)
        (ComplexShape.up ℕ) q)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS q
  have hg_surj : Function.Surjective (S.g.f q).hom :=
    (ModuleCat.epi_iff_surjective (S.g.f q)).mp hSq.epi_g
  let y : S.X₂.X q := Classical.choose (hg_surj ((S.X₃.iCycles q).hom z))
  have hy : (S.g.f q).hom y = (S.X₃.iCycles q).hom z :=
    Classical.choose_spec (hg_surj ((S.X₃.iCycles q).hom z))
  have hdy :
      (S.g.f (q + 1)).hom ((S.X₂.d q (q + 1)).hom y) = 0 := by
    have hcomm := ConcreteCategory.congr_hom (S.g.comm q (q + 1)) y
    simp only [moduleHom_comp_apply] at hcomm
    rw [← hcomm, hy]
    exact ConcreteCategory.congr_hom (S.X₃.iCycles_d q (q + 1)) z
  have hSq1 : (S.map
      (HomologicalComplex.eval (ModuleCat.{u} R)
        (ComplexShape.up ℕ) (q + 1))).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS (q + 1)
  obtain ⟨a, ha⟩ :=
    ((S.map (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.up ℕ) (q + 1))).moduleCat_exact_iff.mp hSq1.exact)
      ((S.X₂.d q (q + 1)).hom y) hdy
  let aCycle : S.X₁.cycles (q + 1) :=
    S.X₁.cyclesMk a (q + 2) (CochainComplex.next ℕ (q + 1))
      (hS.d_eq_zero_of_f_eq_d_apply q (q + 1) y a ha (q + 2))
  have haCycle_i : (S.X₁.iCycles (q + 1)).hom aCycle = a := by
    change ((forget₂ (ModuleCat R) Ab).map (S.X₁.iCycles (q + 1)))
      aCycle = a
    exact HomologicalComplex.i_cyclesMk _ _ _ _ _
  have hdeltaS :
      (hS.δ q (q + 1) rfl).hom ((S.X₃.homologyπ q).hom z) =
        (S.X₁.homologyπ (q + 1)).hom aCycle :=
    delta_apply_cycles R hS q z y hy a ha
  let zT : T.X₃.cycles (p + q) :=
    (P₃.pairCycles p q).hom (x ⊗ₜ[R] z)
  let w : T.X₂.X (p + q) :=
    (P₂.pair p q).hom ((K.iCycles p).hom x ⊗ₜ[R] y)
  have hwg : (T.g.f (p + q)).hom w = (T.X₃.iCycles (p + q)).hom zT := by
    have hcompat := ConcreteCategory.congr_hom (hpair_g p q)
      ((K.iCycles p).hom x ⊗ₜ[R] y)
    simp only [moduleHom_comp_apply, moduleTensorHom_tmul] at hcompat
    rw [hy] at hcompat
    have hzT := pairCycles_i_apply R P₃ p q x z
    exact hcompat.trans hzT.symm
  let e : p + (q + 1) = p + q + 1 := by omega
  let b₀ : T.X₁.X (p + q + 1) :=
    (T.X₁.XIsoOfEq e).hom.hom
      ((P₁.pair p (q + 1)).hom ((K.iCycles p).hom x ⊗ₜ[R] a))
  let s : ℤ := (-1 : ℤ) ^ p
  let b : T.X₁.X (p + q + 1) := s • b₀
  have hbf : (T.f.f (p + q + 1)).hom b =
      (T.X₂.d (p + q) (p + q + 1)).hom w := by
    exact right_preimage_eq_d R P₁ P₂ hpair_f p q x y a ha
  let bCycle : T.X₁.cycles (p + q + 1) :=
    T.X₁.cyclesMk b (p + q + 2)
      (CochainComplex.next ℕ (p + q + 1))
      (hT.d_eq_zero_of_f_eq_d_apply (p + q) (p + q + 1) w b hbf
        (p + q + 2))
  have hbCycle_i : (T.X₁.iCycles (p + q + 1)).hom bCycle = b := by
    change ((forget₂ (ModuleCat R) Ab).map
      (T.X₁.iCycles (p + q + 1))) bCycle = b
    exact HomologicalComplex.i_cyclesMk _ _ _ _ _
  have hdeltaT :
      (hT.δ (p + q) (p + q + 1) rfl).hom
          ((T.X₃.homologyπ (p + q)).hom zT) =
        (T.X₁.homologyπ (p + q + 1)).hom bCycle :=
    delta_apply_cycles R hT (p + q) zT w hwg b hbf
  let c₀ : T.X₁.cycles (p + (q + 1)) :=
    (P₁.pairCycles p (q + 1)).hom (x ⊗ₜ[R] aCycle)
  let c : T.X₁.cycles (p + q + 1) :=
    (T.X₁.cyclesIsoOfEq e).hom.hom c₀
  have hc_eq : c = s • bCycle := by
    apply (ModuleCat.mono_iff_injective
      (f := T.X₁.iCycles (p + q + 1))).mp inferInstance
    have hc_i := ConcreteCategory.congr_hom
      (T.X₁.cyclesIsoOfEq_hom_iCycles e) c₀
    have hc_i' :
        (T.X₁.iCycles (p + q + 1)).hom c =
          (T.X₁.XIsoOfEq e).hom.hom
            ((T.X₁.iCycles (p + (q + 1))).hom c₀) := by
      simpa only [moduleHom_comp_apply] using hc_i
    have hc₀_i := pairCycles_i_apply R P₁ p (q + 1) x aCycle
    change (T.X₁.iCycles (p + q + 1)).hom c =
      (T.X₁.iCycles (p + q + 1)).hom (s • bCycle)
    rw [map_zsmul, hbCycle_i]
    change _ = s • (s • b₀)
    rw [← mul_smul]
    have hs : s * s = 1 := by
      dsimp only [s]
      rw [← pow_add, ← two_mul]
      simp
    rw [hs, one_smul]
    change (T.X₁.iCycles (p + q + 1)).hom c = b₀
    rw [hc_i', hc₀_i, haCycle_i]
  rw [hdeltaS]
  rw [pairHomology_π_apply R P₁ p (q + 1) x aCycle]
  have htransport := ConcreteCategory.congr_hom
    (T.X₁.homologyπ_comp_homologyIsoOfEq_hom e) c₀
  have htransport' :
      (T.X₁.homologyIsoOfEq e).hom.hom
          ((T.X₁.homologyπ (p + (q + 1))).hom c₀) =
        (T.X₁.homologyπ (p + q + 1)).hom c := by
    simpa only [moduleHom_comp_apply] using htransport
  rw [htransport']
  rw [pairHomology_π_apply R P₃ p q x z]
  rw [hdeltaT]
  rw [← map_zsmul, ← hc_eq]

/-- Right input connecting map has the left degree Koszul sign.

For compatible pairings `K × S_i → T_i` on short exact sequences `S` and `T`, pairing after
the right connecting map in degree `q` equals `(-1)^p` times pairing in degrees `(p,q)`
followed by the target connecting map, after degree transport. -/
theorem pairHomology_delta_right
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (P₁ : CochainGradedPairing K S.X₁ T.X₁)
    (P₂ : CochainGradedPairing K S.X₂ T.X₂)
    (P₃ : CochainGradedPairing K S.X₃ T.X₃)
    (hpair_f : ∀ p q, P₁.pair p q ≫ T.f.f (p + q) =
      (𝟙 (K.X p) ⊗ₘ S.f.f q) ≫ P₂.pair p q)
    (hpair_g : ∀ p q, P₂.pair p q ≫ T.g.f (p + q) =
      (𝟙 (K.X p) ⊗ₘ S.g.f q) ≫ P₃.pair p q)
    (p q : ℕ) :
    ((𝟙 (K.homology p) ⊗ₘ hS.δ q (q + 1) rfl) ≫
        P₁.pairHomology p (q + 1) ≫
        (T.X₁.homologyIsoOfEq
          (show p + (q + 1) = p + q + 1 by omega)).hom) =
      ((-1 : ℤ) ^ p) •
        (P₃.pairHomology p q ≫
          hT.δ (p + q) (p + q + 1) rfl) := by
  apply tensor_homologyπ_hom_ext K ((ComplexShape.up ℕ).prev p) p rfl
    S.X₃ ((ComplexShape.up ℕ).prev q) q rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simpa only [map_add] using congrArg₂ (· + ·) ht₁ ht₂
  | tmul x z =>
      simpa only [moduleHom_comp_apply, moduleTensorHom_tmul,
        moduleHom_zsmul_apply, ModuleCat.id_apply] using
        pairHomology_delta_right_apply_cycles R hS hT P₁ P₂ P₃
          hpair_f hpair_g p q x z

private theorem left_preimage_eq_d
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (P₁ : CochainGradedPairing S.X₁ K T.X₁)
    (P₂ : CochainGradedPairing S.X₂ K T.X₂)
    (hpair_f : ∀ p q, P₁.pair p q ≫ T.f.f (p + q) =
      (S.f.f p ⊗ₘ 𝟙 (K.X q)) ≫ P₂.pair p q)
    (p q : ℕ) (y : S.X₂.X p) (x : K.cycles q)
    (a : S.X₁.X (p + 1))
    (ha : (S.f.f (p + 1)).hom a =
      (S.X₂.d p (p + 1)).hom y) :
    (T.f.f (p + q + 1)).hom
        ((T.X₁.XIsoOfEq
          (show (p + 1) + q = p + q + 1 by omega)).hom.hom
          ((P₁.pair (p + 1) q).hom
            (a ⊗ₜ[R] (K.iCycles q).hom x))) =
      (T.X₂.d (p + q) (p + q + 1)).hom
        ((P₂.pair p q).hom (y ⊗ₜ[R] (K.iCycles q).hom x)) := by
  rw [P₂.pair_d_left_of_cycle R p q y x]
  let e : (p + 1) + q = p + q + 1 := by omega
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.XIsoOfEq_hom_naturality T.f e)
    ((P₁.pair (p + 1) q).hom (a ⊗ₜ[R] (K.iCycles q).hom x))
  symm at hnat
  have hnat' :
      (T.f.f (p + q + 1)).hom
          ((T.X₁.XIsoOfEq e).hom.hom
            ((P₁.pair (p + 1) q).hom
              (a ⊗ₜ[R] (K.iCycles q).hom x))) =
        (T.X₂.XIsoOfEq e).hom.hom
          ((T.f.f ((p + 1) + q)).hom
            ((P₁.pair (p + 1) q).hom
              (a ⊗ₜ[R] (K.iCycles q).hom x))) := by
    simpa only [moduleHom_comp_apply] using hnat
  rw [hnat']
  have hcompat := ConcreteCategory.congr_hom (hpair_f (p + 1) q)
    (a ⊗ₜ[R] (K.iCycles q).hom x)
  simp only [moduleHom_comp_apply, moduleTensorHom_tmul] at hcompat
  rw [hcompat, ha]
  simp

private theorem pairHomology_delta_left_apply_cycles
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (P₁ : CochainGradedPairing S.X₁ K T.X₁)
    (P₂ : CochainGradedPairing S.X₂ K T.X₂)
    (P₃ : CochainGradedPairing S.X₃ K T.X₃)
    (hpair_f : ∀ p q, P₁.pair p q ≫ T.f.f (p + q) =
      (S.f.f p ⊗ₘ 𝟙 (K.X q)) ≫ P₂.pair p q)
    (hpair_g : ∀ p q, P₂.pair p q ≫ T.g.f (p + q) =
      (S.g.f p ⊗ₘ 𝟙 (K.X q)) ≫ P₃.pair p q)
    (p q : ℕ) (z : S.X₃.cycles p) (x : K.cycles q) :
    (T.X₁.homologyIsoOfEq
        (show (p + 1) + q = p + q + 1 by omega)).hom.hom
      ((P₁.pairHomology (p + 1) q).hom
        ((hS.δ p (p + 1) rfl).hom ((S.X₃.homologyπ p).hom z) ⊗ₜ[R]
          (K.homologyπ q).hom x)) =
      (hT.δ (p + q) (p + q + 1) rfl).hom
        ((P₃.pairHomology p q).hom
          ((S.X₃.homologyπ p).hom z ⊗ₜ[R]
            (K.homologyπ q).hom x)) := by
  have hSp : (S.map
      (HomologicalComplex.eval (ModuleCat.{u} R)
        (ComplexShape.up ℕ) p)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS p
  have hg_surj : Function.Surjective (S.g.f p).hom :=
    (ModuleCat.epi_iff_surjective (S.g.f p)).mp hSp.epi_g
  let y : S.X₂.X p := Classical.choose (hg_surj ((S.X₃.iCycles p).hom z))
  have hy : (S.g.f p).hom y = (S.X₃.iCycles p).hom z :=
    Classical.choose_spec (hg_surj ((S.X₃.iCycles p).hom z))
  have hdy :
      (S.g.f (p + 1)).hom ((S.X₂.d p (p + 1)).hom y) = 0 := by
    have hcomm := ConcreteCategory.congr_hom (S.g.comm p (p + 1)) y
    simp only [moduleHom_comp_apply] at hcomm
    rw [← hcomm, hy]
    exact ConcreteCategory.congr_hom (S.X₃.iCycles_d p (p + 1)) z
  have hSp1 : (S.map
      (HomologicalComplex.eval (ModuleCat.{u} R)
        (ComplexShape.up ℕ) (p + 1))).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS (p + 1)
  obtain ⟨a, ha⟩ :=
    ((S.map (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.up ℕ) (p + 1))).moduleCat_exact_iff.mp hSp1.exact)
      ((S.X₂.d p (p + 1)).hom y) hdy
  let aCycle : S.X₁.cycles (p + 1) :=
    S.X₁.cyclesMk a (p + 2) (CochainComplex.next ℕ (p + 1))
      (hS.d_eq_zero_of_f_eq_d_apply p (p + 1) y a ha (p + 2))
  have haCycle_i : (S.X₁.iCycles (p + 1)).hom aCycle = a := by
    change ((forget₂ (ModuleCat R) Ab).map (S.X₁.iCycles (p + 1)))
      aCycle = a
    exact HomologicalComplex.i_cyclesMk _ _ _ _ _
  have hdeltaS :
      (hS.δ p (p + 1) rfl).hom ((S.X₃.homologyπ p).hom z) =
        (S.X₁.homologyπ (p + 1)).hom aCycle :=
    delta_apply_cycles R hS p z y hy a ha
  let zT : T.X₃.cycles (p + q) :=
    (P₃.pairCycles p q).hom (z ⊗ₜ[R] x)
  let w : T.X₂.X (p + q) :=
    (P₂.pair p q).hom (y ⊗ₜ[R] (K.iCycles q).hom x)
  have hwg : (T.g.f (p + q)).hom w = (T.X₃.iCycles (p + q)).hom zT := by
    have hcompat := ConcreteCategory.congr_hom (hpair_g p q)
      (y ⊗ₜ[R] (K.iCycles q).hom x)
    simp only [moduleHom_comp_apply, moduleTensorHom_tmul] at hcompat
    rw [hy] at hcompat
    have hzT := pairCycles_i_apply R P₃ p q z x
    exact hcompat.trans hzT.symm
  let e : (p + 1) + q = p + q + 1 := by omega
  let b : T.X₁.X (p + q + 1) :=
    (T.X₁.XIsoOfEq e).hom.hom
      ((P₁.pair (p + 1) q).hom (a ⊗ₜ[R] (K.iCycles q).hom x))
  have hbf : (T.f.f (p + q + 1)).hom b =
      (T.X₂.d (p + q) (p + q + 1)).hom w := by
    exact left_preimage_eq_d R P₁ P₂ hpair_f p q y x a ha
  let bCycle : T.X₁.cycles (p + q + 1) :=
    T.X₁.cyclesMk b (p + q + 2)
      (CochainComplex.next ℕ (p + q + 1))
      (hT.d_eq_zero_of_f_eq_d_apply (p + q) (p + q + 1) w b hbf
        (p + q + 2))
  have hbCycle_i : (T.X₁.iCycles (p + q + 1)).hom bCycle = b := by
    change ((forget₂ (ModuleCat R) Ab).map
      (T.X₁.iCycles (p + q + 1))) bCycle = b
    exact HomologicalComplex.i_cyclesMk _ _ _ _ _
  have hdeltaT :
      (hT.δ (p + q) (p + q + 1) rfl).hom
          ((T.X₃.homologyπ (p + q)).hom zT) =
        (T.X₁.homologyπ (p + q + 1)).hom bCycle :=
    delta_apply_cycles R hT (p + q) zT w hwg b hbf
  let c₀ : T.X₁.cycles ((p + 1) + q) :=
    (P₁.pairCycles (p + 1) q).hom (aCycle ⊗ₜ[R] x)
  let c : T.X₁.cycles (p + q + 1) :=
    (T.X₁.cyclesIsoOfEq e).hom.hom c₀
  have hc_eq : c = bCycle := by
    apply (ModuleCat.mono_iff_injective
      (f := T.X₁.iCycles (p + q + 1))).mp inferInstance
    have hc_i := ConcreteCategory.congr_hom
      (T.X₁.cyclesIsoOfEq_hom_iCycles e) c₀
    have hc_i' :
        (T.X₁.iCycles (p + q + 1)).hom c =
          (T.X₁.XIsoOfEq e).hom.hom
            ((T.X₁.iCycles ((p + 1) + q)).hom c₀) := by
      simpa only [moduleHom_comp_apply] using hc_i
    have hc₀_i := pairCycles_i_apply R P₁ (p + 1) q aCycle x
    change (T.X₁.iCycles (p + q + 1)).hom c =
      (T.X₁.iCycles (p + q + 1)).hom bCycle
    rw [hc_i', hc₀_i, haCycle_i, hbCycle_i]
  rw [hdeltaS]
  rw [pairHomology_π_apply R P₁ (p + 1) q aCycle x]
  have htransport := ConcreteCategory.congr_hom
    (T.X₁.homologyπ_comp_homologyIsoOfEq_hom e) c₀
  have htransport' :
      (T.X₁.homologyIsoOfEq e).hom.hom
          ((T.X₁.homologyπ ((p + 1) + q)).hom c₀) =
        (T.X₁.homologyπ (p + q + 1)).hom c := by
    simpa only [moduleHom_comp_apply] using htransport
  rw [htransport']
  rw [pairHomology_π_apply R P₃ p q z x]
  rw [hdeltaT, hc_eq]

/-- Left input connecting map commutes with homology pairing.

For compatible pairings `S_i × K → T_i` on short exact sequences, applying the left connecting
map before pairing equals pairing first and applying the target connecting map, with degree
transport to `p + q + 1` and coefficient one. -/
theorem pairHomology_delta_left
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (P₁ : CochainGradedPairing S.X₁ K T.X₁)
    (P₂ : CochainGradedPairing S.X₂ K T.X₂)
    (P₃ : CochainGradedPairing S.X₃ K T.X₃)
    (hpair_f : ∀ p q, P₁.pair p q ≫ T.f.f (p + q) =
      (S.f.f p ⊗ₘ 𝟙 (K.X q)) ≫ P₂.pair p q)
    (hpair_g : ∀ p q, P₂.pair p q ≫ T.g.f (p + q) =
      (S.g.f p ⊗ₘ 𝟙 (K.X q)) ≫ P₃.pair p q)
    (p q : ℕ) :
    ((hS.δ p (p + 1) rfl ⊗ₘ 𝟙 (K.homology q)) ≫
        P₁.pairHomology (p + 1) q ≫
        (T.X₁.homologyIsoOfEq
          (show (p + 1) + q = p + q + 1 by omega)).hom) =
      P₃.pairHomology p q ≫
        hT.δ (p + q) (p + q + 1) rfl := by
  apply tensor_homologyπ_hom_ext S.X₃ ((ComplexShape.up ℕ).prev p) p rfl
    K ((ComplexShape.up ℕ).prev q) q rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simpa only [map_add] using congrArg₂ (· + ·) ht₁ ht₂
  | tmul z x =>
      simpa only [moduleHom_comp_apply, moduleTensorHom_tmul,
        ModuleCat.id_apply] using
        pairHomology_delta_left_apply_cycles R hS hT P₁ P₂ P₃
          hpair_f hpair_g p q z x

end HomologicalComplex.CochainGradedPairing
