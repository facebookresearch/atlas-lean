/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IterCech_augTot_single_eq_augCech_cup_zero.lean`
and
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_IterCech_augTot_single_eq_augCech_cup_zero.lean`
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

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.IterCech
public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.Cup
public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.CochainPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic.FinCases

/-!
# Degree-zero compatibility of the iterated Čech restriction maps with the cup product

Let `X` and `Y` be schemes over `Spec k` with ordered affine covers `𝔘` and `𝔙`, and cover
`X ×_k Y` by the products `pr₁⁻¹ 𝔘ᵢ ⊓ pr₂⁻¹ 𝔙ⱼ`, assumed affine. For degree-zero Čech cocycles
`α` of `𝒪_X` and `β` of `𝒪_Y`, the external product `pr₁^* α · pr₂^* β`, viewed as a total
cochain of the Čech double complex and restricted into the iterated Čech complex by `augTot`,
agrees with the image under `augCech` of the cup product of the pullbacks of `α` and `β` to the
product cover.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OModulePresheaf.IterCech

section Aux

variable {k : Type u} [CommRing k] {X P : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of k)}

private theorem map_app_eq_appLE (f : P ⟶ X) {U : X.Opens} {V : P.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)) :
    (P.presheaf.map (homOfLE e).op).hom ((f.app U).hom x) = (f.appLE U V e).hom x := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem map_appLE' (f : P ⟶ X) {U : X.Opens} {V W : P.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (i : W ≤ V) (x : Γ(X, U)) :
    (P.presheaf.map (homOfLE i).op).hom ((f.appLE U V e).hom x) =
      (f.appLE U W (i.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem map_map_app_eq_appLE (f : P ⟶ X) {U : X.Opens} {V W : P.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (i : W ≤ V) (x : Γ(X, U)) :
    (P.presheaf.map (homOfLE i).op).hom ((P.presheaf.map (homOfLE e).op).hom ((f.app U).hom x)) =
      (f.appLE U W (i.trans e)).hom x := by
  rw [map_app_eq_appLE, map_appLE']

private theorem map_map_map_app_eq_appLE (f : P ⟶ X) {U : X.Opens} {V W O : P.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (i : W ≤ V) (j : O ≤ W) (x : Γ(X, U)) :
    (P.presheaf.map (homOfLE j).op).hom ((P.presheaf.map (homOfLE i).op).hom
      ((P.presheaf.map (homOfLE e).op).hom ((f.app U).hom x))) =
      (f.appLE U O (j.trans (i.trans e))).hom x := by
  rw [map_map_app_eq_appLE, map_appLE']

private theorem appLE_map_res (f : P ⟶ X) {U U' : X.Opens} {V : P.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (i : U ≤ U') (x : Γ(X, U')) (e' : V ≤ f ⁻¹ᵁ U') :
    (f.appLE U V e).hom ((X.presheaf.map (homOfLE i).op).hom x) = (f.appLE U' V e').hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The strictly increasing pair `(a, b)`. -/
private def pairIdx (𝔘 : X.OrderedAffineCover) {a b : 𝔘.ι} (hab : a < b) : 𝔘.Idx 1 :=
  ⟨![a, b], by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all⟩

private theorem appLE_cocycle_zero_of_lt (f : P ⟶ X) (𝔘 : X.OrderedAffineCover)
    (α : (unit πX).cochain 𝔘 0) (hα : (unit πX).d 𝔘 0 α = 0) (s s' : 𝔘.Idx 0)
    (hlt : s.1 0 < s'.1 0) (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.inter s)
    (h' : O ≤ f ⁻¹ᵁ 𝔘.inter s') :
    (f.appLE _ O h).hom (α s) = (f.appLE _ O h').hom (α s') := by
  set w := pairIdx 𝔘 hlt
  have h0 : 𝔘.face w 0 = s' := Subtype.ext (funext fun x => by fin_cases x; rfl)
  have h1 : 𝔘.face w 1 = s := Subtype.ext (funext fun x => by fin_cases x; rfl)
  have hw : O ≤ f ⁻¹ᵁ 𝔘.inter w := by
    change O ≤ f ⁻¹ᵁ (⨅ j, 𝔘.U (w.1 j))
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    refine le_iInf fun j => ?_
    fin_cases j
    · exact h.trans (f.preimage_mono (𝔘.inter_le s 0))
    · exact h'.trans (f.preimage_mono (𝔘.inter_le s' 0))
  have key := congrFun hα w
  rw [d_apply, Fin.sum_univ_two] at key
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Pi.zero_apply] at key
  have e := congrArg (fun x : Γ(X, 𝔘.inter w) => (f.appLE _ O hw).hom x) (add_neg_eq_zero.1 key)
  have step : ∀ (u : 𝔘.Idx 0) (hle : 𝔘.inter w ≤ 𝔘.inter u) (hO : O ≤ f ⁻¹ᵁ 𝔘.inter u),
      (f.appLE _ O hw).hom ((unit πX).res hle (α u)) = (f.appLE _ O hO).hom (α u) :=
    fun u hle hO => appLE_map_res f hw hle _ hO
  have gen : ∀ (j : Fin 2) (u : 𝔘.Idx 0) (_ : 𝔘.face w j = u) (hO : O ≤ f ⁻¹ᵁ 𝔘.inter u),
      (f.appLE _ O hO).hom (α u) =
        (f.appLE _ O hw).hom ((unit πX).res (𝔘.inter_le_inter_face w j) (α (𝔘.face w j))) := by
    rintro j u rfl hO
    exact (step _ _ hO).symm
  rw [gen 1 s h1 h, gen 0 s' h0 h']
  exact e.symm

private theorem appLE_cocycle_zero (f : P ⟶ X) (𝔘 : X.OrderedAffineCover)
    (α : (unit πX).cochain 𝔘 0) (hα : (unit πX).d 𝔘 0 α = 0) (s s' : 𝔘.Idx 0)
    (O : P.Opens) (h : O ≤ f ⁻¹ᵁ 𝔘.inter s) (h' : O ≤ f ⁻¹ᵁ 𝔘.inter s') :
    (f.appLE _ O h).hom (α s) = (f.appLE _ O h').hom (α s') := by
  rcases lt_trichotomy (s.1 0) (s'.1 0) with hlt | heq | hgt
  · exact appLE_cocycle_zero_of_lt f 𝔘 α hα s s' hlt O h h'
  · obtain rfl : s = s' := Subtype.ext (funext fun x => by fin_cases x; exact heq)
    rfl
  · exact (appLE_cocycle_zero_of_lt f 𝔘 α hα s' s hgt O h' h).symm

private theorem unitPullback_zero {R' : Type u} [CommRing R'] {πP : P ⟶ Spec (.of R')}
    (f : P ⟶ X) (𝒲 : P.OrderedAffineCover) (𝔘 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔘.ι)
    (hlam : ∀ w, 𝒲.U w ≤ f ⁻¹ᵁ 𝔘.U (lam w)) (α : (unit πX).cochain 𝔘 0) (s : 𝒲.Idx 0) :
    ∃ (t : 𝔘.Idx 0) (e : 𝒲.inter s ≤ f ⁻¹ᵁ 𝔘.inter t),
      unitPullback (πX := πP) f 𝒲 𝔘 lam hlam 0 α s =
        (P.presheaf.map (homOfLE e).op).hom ((f.app (𝔘.inter t)).hom (α t)) := by
  have hinj : Function.Injective (lam ∘ s.1) := fun a b _ => Subsingleton.elim (α := Fin 1) a b
  refine ⟨𝒲.sortIdx 𝔘 lam s hinj, 𝒲.inter_le_preimage_inter_sortIdx f 𝔘 lam hlam s hinj, ?_⟩
  have hsort : Tuple.sort (lam ∘ s.1) = 1 :=
    Equiv.ext fun x => Subsingleton.elim (α := Fin 1) _ _
  rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
    show ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) = 1 by
      rw [hsort, Equiv.Perm.sign_one, Units.val_one], one_smul]

end Aux

/-- Degree-zero compatibility of the restriction maps `augTot` and `augCech` with the cup product
on the product cover of `X ×_k Y`: for Čech `0`-cocycles `α` of `𝒪_X` on `𝔘` and `β` of `𝒪_Y`
on `𝔙`, `augTot` sends the external product `pr₁^* α · pr₂^* β` (a total `0`-cochain of the Čech
double complex) to the same element of the iterated Čech term `IterCech.C … 0 0` as `augCech`
sends the cup product of the pullbacks of `α` and `β` to the product cover. -/
theorem augTot_single_eq_augCech_cup_zero
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓
      (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓
        (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)
    (i : DoubleComplex.Diag 0)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
    (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2))) :
    (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
              (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily
            0
            (Pi.single i
              (fun st : 𝔘.Idx i.1.1 × 𝔙.Idx i.1.2 =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY)
                      (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α.1 st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY)
                      (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β.1 st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
                  (𝔘.preimageFamily (pullback.fst πX πY))
                  (𝔙.preimageFamily (pullback.snd πX πY)) i.1.1 i.1.2) :
              DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech
                (𝔘.preimageFamily (pullback.fst πX πY))
                (𝔙.preimageFamily (pullback.snd πX πY))) 0))
      = (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
              (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
            0
            ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
                (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 0 i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
                  (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun _ => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
                  (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun _ => inf_le_right) i.1.2 β.1))) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  simp only at hpq
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := ⟨by omega, by omega⟩
  have hα : (OModulePresheaf.unit πX).d 𝔘 0 α.1 = 0 := LinearMap.mem_ker.1 α.2
  have hβ : (OModulePresheaf.unit πY).d 𝔙 0 β.1 = 0 := LinearMap.mem_ker.1 β.2
  funext K pq st
  obtain ⟨⟨a, b⟩, hab⟩ := pq
  simp only at hab
  obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
  rw [augTot_apply, resTot₀_apply]
  erw [Pi.single_eq_same]
  rw [unit_res_apply]
  rw [augCech_apply]
  erw [cup_apply]
  rw [res_smul, unit_res_apply, unit_res_apply]
  obtain ⟨t₁, e₁, h₁⟩ := unitPullback_zero (πP := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
    _ 𝔘 _ (fun ij => inf_le_left) α.1 (Scheme.OrderedAffineCover.frontFace _ 0 0 0 rfl K)
  obtain ⟨t₂, e₂, h₂⟩ := unitPullback_zero (πP := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
    _ 𝔙 _ (fun ij => inf_le_right) β.1 (Scheme.OrderedAffineCover.backFace _ 0 0 0 rfl K)
  erw [h₁, h₂, map_mul]
  exact congrArg₂ (· * ·)
    ((map_map_app_eq_appLE _ _ _ _).trans ((appLE_cocycle_zero _ 𝔘 α.1 hα _ _ _ _ _).trans
      (map_map_map_app_eq_appLE _ _ _ _ _).symm))
    ((map_map_app_eq_appLE _ _ _ _).trans ((appLE_cocycle_zero _ 𝔙 β.1 hβ _ _ _ _ _).trans
      (map_map_map_app_eq_appLE _ _ _ _ _).symm))

end AlgebraicGeometry.OModulePresheaf.IterCech
