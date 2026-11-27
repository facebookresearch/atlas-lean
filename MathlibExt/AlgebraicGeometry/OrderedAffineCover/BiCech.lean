/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_BiCech.lean`
and
`Definitions/Def_AlgebraicGeometry_BoundedCochainTensor.lean`
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

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.Cech
public import MathlibExt.Algebra.Homology.BoundedDoubleComplex

/-!
# The Čech double complex of two ordered open families

For two finite ordered families of opens `𝔄`, `𝔅` of a scheme and a presheaf of modules `F`,
`OModulePresheaf.biCech F 𝔄 𝔅` is the double complex with
`C p q = ∏_{s ∈ 𝔄.Idx p, t ∈ 𝔅.Idx q} F(𝔄.inter s ⊓ 𝔅.inter t)` and the two alternating Čech
differentials. We also define the product cover `prodCover` of two families whose pairwise
intersections are affine and cover the scheme, indexed lexicographically.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite, linearly ordered family of opens of `Z` (not required to be affine or to cover). -/
structure Scheme.OrderedOpenFamily (Z : Scheme.{u}) where
  /-- The index type. -/
  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]
  /-- The opens of the family. -/
  U : ι → Z.Opens

attribute [instance] Scheme.OrderedOpenFamily.instFintype
  Scheme.OrderedOpenFamily.instLinearOrder

namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔄 : Z.OrderedOpenFamily)

/-- Strictly increasing `(p + 1)`-tuples of indices. -/
def Idx (p : ℕ) : Type u := {s : Fin (p + 1) → 𝔄.ι // StrictMono s}

instance instFintypeIdx (p : ℕ) : Fintype (𝔄.Idx p) := Subtype.fintype _

instance instDecidableEqIdx (p : ℕ) : DecidableEq (𝔄.Idx p) := Classical.decEq _

/-- The intersection of the opens indexed by a tuple. -/
def inter {p : ℕ} (s : 𝔄.Idx p) : Z.Opens := ⨅ j, 𝔄.U (s.1 j)

/-- The `j`-th face of a strictly increasing tuple: delete its `j`-th entry. -/
def face {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) : 𝔄.Idx p :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem face_val {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) :
    (𝔄.face s j).1 = s.1 ∘ Fin.succAbove j := rfl

theorem inter_le {p : ℕ} (s : 𝔄.Idx p) (j : Fin (p + 1)) : 𝔄.inter s ≤ 𝔄.U (s.1 j) :=
  iInf_le _ j

theorem inter_le_inter_face {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) :
    𝔄.inter s ≤ 𝔄.inter (𝔄.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem isEmpty_idx_of_card_le {p : ℕ} (h : Fintype.card 𝔄.ι ≤ p) : IsEmpty (𝔄.Idx p) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  simp only [Fintype.card_fin] at this
  omega

/-- The lexicographically ordered product cover `{𝔄.U i ⊓ 𝔅.U j}` of two families whose
pairwise intersections are affine and cover `Z`. -/
def prodCover (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) : Z.OrderedAffineCover where
  ι := 𝔄.ι ×ₗ 𝔅.ι
  instFintype := inferInstanceAs (Fintype (𝔄.ι × 𝔅.ι))
  instLinearOrder := inferInstance
  U ij := 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2
  isAffineOpen ij := haff _ _
  iSup_eq_top := by
    rw [← hcov]
    exact le_antisymm
      (iSup_le fun ij => le_iSup (fun ij : 𝔄.ι × 𝔅.ι => 𝔄.U ij.1 ⊓ 𝔅.U ij.2) (ofLex ij))
      (iSup_le fun ij =>
        le_iSup (fun ij : 𝔄.ι ×ₗ 𝔅.ι => 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2) (toLex ij))

theorem prodCover_ι (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) :
    (𝔄.prodCover 𝔅 haff hcov).ι = (𝔄.ι ×ₗ 𝔅.ι) := rfl

theorem prodCover_U (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) (ij : 𝔄.ι ×ₗ 𝔅.ι) :
    (𝔄.prodCover 𝔅 haff hcov).U ij = 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2 := rfl

end Scheme.OrderedOpenFamily

namespace Scheme.OrderedAffineCover

/-- An ordered affine cover viewed as an ordered open family. -/
def toOpenFamily {Z : Scheme.{u}} (K : Z.OrderedAffineCover) : Z.OrderedOpenFamily where
  ι := K.ι
  U := K.U

theorem toOpenFamily_ι {Z : Scheme.{u}} (K : Z.OrderedAffineCover) :
    K.toOpenFamily.ι = K.ι := rfl

theorem toOpenFamily_U {Z : Scheme.{u}} (K : Z.OrderedAffineCover) (i : K.ι) :
    K.toOpenFamily.U i = K.U i := rfl

/-- The family of preimages of the opens of a cover along a morphism `q : P ⟶ Y`. -/
@[reducible] def preimageFamily {P Y : Scheme.{u}} (K : Y.OrderedAffineCover) (q : P ⟶ Y) :
    P.OrderedOpenFamily :=
  ⟨K.ι, fun i => q ⁻¹ᵁ K.U i⟩

theorem preimageFamily_ι {P Y : Scheme.{u}} (K : Y.OrderedAffineCover) (q : P ⟶ Y) :
    (K.preimageFamily q).ι = K.ι := rfl

theorem preimageFamily_U {P Y : Scheme.{u}} (K : Y.OrderedAffineCover) (q : P ⟶ Y) (i : K.ι) :
    (K.preimageFamily q).U i = q ⁻¹ᵁ K.U i := rfl

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
variable (𝔄 𝔅 : Z.OrderedOpenFamily)

namespace BiCech

theorem inter_inf_le_left {p q : ℕ} (s : 𝔄.Idx (p + 1)) (t : 𝔅.Idx q) (j : Fin (p + 2)) :
    𝔄.inter s ⊓ 𝔅.inter t ≤ 𝔄.inter (𝔄.face s j) ⊓ 𝔅.inter t :=
  inf_le_inf_right _ (𝔄.inter_le_inter_face s j)

theorem inter_inf_le_right {p q : ℕ} (s : 𝔄.Idx p) (t : 𝔅.Idx (q + 1)) (j : Fin (q + 2)) :
    𝔄.inter s ⊓ 𝔅.inter t ≤ 𝔄.inter s ⊓ 𝔅.inter (𝔅.face t j) :=
  inf_le_inf_left _ (𝔅.inter_le_inter_face t j)

/-- The `(p, q)` term of the Čech double complex. -/
abbrev C (p q : ℕ) : Type u := ∀ st : 𝔄.Idx p × 𝔅.Idx q, F.obj (𝔄.inter st.1 ⊓ 𝔅.inter st.2)

/-- The horizontal Čech differential, in the `𝔄` direction. -/
def dH (p q : ℕ) : C F 𝔄 𝔅 p q →ₗ[R] C F 𝔄 𝔅 (p + 1) q :=
  LinearMap.pi fun st => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (inter_inf_le_left 𝔄 𝔅 st.1 st.2 j)).comp (LinearMap.proj (𝔄.face st.1 j, st.2)))

/-- The vertical Čech differential, in the `𝔅` direction. -/
def dV (p q : ℕ) : C F 𝔄 𝔅 p q →ₗ[R] C F 𝔄 𝔅 p (q + 1) :=
  LinearMap.pi fun st => ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (inter_inf_le_right 𝔄 𝔅 st.1 st.2 j)).comp (LinearMap.proj (st.1, 𝔅.face st.2 j)))

theorem dH_apply (p q : ℕ) (c : C F 𝔄 𝔅 p q) (st : 𝔄.Idx (p + 1) × 𝔅.Idx q) :
    dH F 𝔄 𝔅 p q c st = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      F.res (inter_inf_le_left 𝔄 𝔅 st.1 st.2 j) (c (𝔄.face st.1 j, st.2)) := by
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem dV_apply (p q : ℕ) (c : C F 𝔄 𝔅 p q) (st : 𝔄.Idx p × 𝔅.Idx (q + 1)) :
    dV F 𝔄 𝔅 p q c st = ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      F.res (inter_inf_le_right 𝔄 𝔅 st.1 st.2 j) (c (st.1, 𝔅.face st.2 j)) := by
  simp only [dV, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply,
    LinearMap.proj_apply]

private theorem succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

theorem res_left_eq {p q : ℕ} {s s' : 𝔄.Idx p} (heq : s = s') (t : 𝔅.Idx q) (f : C F 𝔄 𝔅 p q)
    {O : Z.Opens} (h : O ≤ 𝔄.inter s ⊓ 𝔅.inter t) (h' : O ≤ 𝔄.inter s' ⊓ 𝔅.inter t) :
    F.res h (f (s, t)) = F.res h' (f (s', t)) := by
  subst heq; rfl

theorem res_right_eq {p q : ℕ} (s : 𝔄.Idx p) {t t' : 𝔅.Idx q} (heq : t = t') (f : C F 𝔄 𝔅 p q)
    {O : Z.Opens} (h : O ≤ 𝔄.inter s ⊓ 𝔅.inter t) (h' : O ≤ 𝔄.inter s ⊓ 𝔅.inter t') :
    F.res h (f (s, t)) = F.res h' (f (s, t')) := by
  subst heq; rfl

theorem dH_sq (p q : ℕ) : dH F 𝔄 𝔅 (p + 1) q ∘ₗ dH F 𝔄 𝔅 p q = 0 := by
  refine LinearMap.ext fun f => funext fun st => ?_
  obtain ⟨s, t⟩ := st
  rw [LinearMap.comp_apply, dH_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [dH_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  have hres : ∀ (a : Fin (p + 3)) (b : Fin (p + 2)),
      F.res (inter_inf_le_left 𝔄 𝔅 s t a)
          (F.res (inter_inf_le_left 𝔄 𝔅 (𝔄.face s a) t b) (f (𝔄.face (𝔄.face s a) b, t)))
        = F.res ((inter_inf_le_left 𝔄 𝔅 s t a).trans (inter_inf_le_left 𝔄 𝔅 (𝔄.face s a) t b))
            (f (𝔄.face (𝔄.face s a) b, t)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (F.res_comp _ _)) _).symm
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (p + 3) × Fin (p + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1
        (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ (congrArg Prod.fst heq))
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (p + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : 𝔄.face (𝔄.face s a) b = 𝔄.face (𝔄.face s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) =
        s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (p + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact res_left_eq F 𝔄 𝔅 hface t f _ _

theorem dV_sq (p q : ℕ) : dV F 𝔄 𝔅 p (q + 1) ∘ₗ dV F 𝔄 𝔅 p q = 0 := by
  refine LinearMap.ext fun f => funext fun st => ?_
  obtain ⟨s, t⟩ := st
  rw [LinearMap.comp_apply, dV_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [dV_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  have hres : ∀ (a : Fin (q + 3)) (b : Fin (q + 2)),
      F.res (inter_inf_le_right 𝔄 𝔅 s t a)
          (F.res (inter_inf_le_right 𝔄 𝔅 s (𝔅.face t a) b) (f (s, 𝔅.face (𝔅.face t a) b)))
        = F.res ((inter_inf_le_right 𝔄 𝔅 s t a).trans (inter_inf_le_right 𝔄 𝔅 s (𝔅.face t a) b))
            (f (s, 𝔅.face (𝔅.face t a) b)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (F.res_comp _ _)) _).symm
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (q + 3) × Fin (q + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1
        (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ (congrArg Prod.fst heq))
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (q + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : 𝔅.face (𝔅.face t a) b = 𝔅.face (𝔅.face t b.succ) a' := by
      apply Subtype.ext
      change t.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) =
        t.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (q + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact res_right_eq F 𝔄 𝔅 s hface f _ _

theorem dHV_comm (p q : ℕ) :
    dV F 𝔄 𝔅 (p + 1) q ∘ₗ dH F 𝔄 𝔅 p q = dH F 𝔄 𝔅 p (q + 1) ∘ₗ dV F 𝔄 𝔅 p q := by
  refine LinearMap.ext fun f => funext fun st => ?_
  obtain ⟨s, t⟩ := st
  simp only [LinearMap.comp_apply, dH_apply, dV_apply, map_sum, map_zsmul, Finset.smul_sum,
    smul_smul,
    OModulePresheaf.res_res]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

end BiCech

/-- The bounded Čech double complex of `F` on the families `𝔄` and `𝔅`. -/
@[reducible] def biCech : DoubleComplex.Bounded R where
  C := BiCech.C F 𝔄 𝔅
  dH := BiCech.dH F 𝔄 𝔅
  dV := BiCech.dV F 𝔄 𝔅
  dH_sq := BiCech.dH_sq F 𝔄 𝔅
  dV_sq := BiCech.dV_sq F 𝔄 𝔅
  dHV_comm := BiCech.dHV_comm F 𝔄 𝔅
  N := max (Fintype.card 𝔄.ι) (Fintype.card 𝔅.ι)
  hBound p q h := by
    rcases h with h | h
    · have := 𝔄.isEmpty_idx_of_card_le ((le_max_left _ _).trans h)
      infer_instance
    · have := 𝔅.isEmpty_idx_of_card_le ((le_max_right _ _).trans h)
      infer_instance

theorem biCech_C (p q : ℕ) : (F.biCech 𝔄 𝔅).C p q = BiCech.C F 𝔄 𝔅 p q := rfl
theorem biCech_N : (F.biCech 𝔄 𝔅).N = max (Fintype.card 𝔄.ι) (Fintype.card 𝔅.ι) := rfl
theorem biCech_dH (p q : ℕ) : (F.biCech 𝔄 𝔅).dH p q = BiCech.dH F 𝔄 𝔅 p q := rfl
theorem biCech_dV (p q : ℕ) : (F.biCech 𝔄 𝔅).dV p q = BiCech.dV F 𝔄 𝔅 p q := rfl

end OModulePresheaf

end AlgebraicGeometry
