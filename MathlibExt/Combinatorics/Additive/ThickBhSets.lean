/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import MathlibExt.Combinatorics.Additive.BhSet
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Constructing thick `B_h`-sets: Bose's construction

Bose's construction of `B_h`-sets in cyclic groups, following Kevin O'Bryant,
*Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27 (2024), Article 24.1.2.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Bose set.** Let $F$ be a finite field with $q$ elements, $K$ a field extension
of $F$, $h$ and $b$ natural numbers and $\theta \in K$. The generalized Bose set
$\mathrm{Bose}_h(q, b)$ is the set of residues $a \in \mathbb{Z}/(q^h - 1)\mathbb{Z}$ such that
$\theta^a = \theta^b + v$ for some $v \in F$, where $\theta^a$ is computed with the least
nonnegative representative of $a$ (for $h = 0$ the modulus is $0$, $a$ ranges over $\mathbb{Z}$
and $\theta^a$ means $\theta^{|a|}$).

In the paper $K$ has degree $h$ over $F$ and $\theta$ generates $K^\times$; the definition does
not need these assumptions.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 1. -/
public def boseSet (F : Type*) {K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) : Set (ZMod (Fintype.card F ^ h - 1)) :=
  {a | ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v}

private theorem cardK {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hK : Module.finrank F K = h) :
    Fintype.card K = Fintype.card F ^ h := by
  rw [Module.card_eq_pow_finrank (K := F), hK]

private theorem orderM {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) :
    orderOf θ = Fintype.card F ^ h - 1 := by
  rw [hθ, cardK hK]

private theorem posM {F : Type*} [Field F] [Fintype F] {h : ℕ} (hh : 2 ≤ h) :
    0 < Fintype.card F ^ h - 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hh0 : h ≠ 0 := by omega
  have hpow : 1 < Fintype.card F ^ h := Nat.one_lt_pow hh0 hq
  omega

private theorem neZeroM {F : Type*} [Field F] [Fintype F] {h : ℕ} (hh : 2 ≤ h) :
    NeZero (Fintype.card F ^ h - 1) :=
  ⟨(posM hh).ne'⟩

private theorem ordPos {K : Type*} [Field K] [Fintype K] {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) : 0 < orderOf θ := by
  rw [hθ]
  have hK : 1 < Fintype.card K := Fintype.one_lt_card
  omega

private theorem theta_ne_zero {K : Type*} [Field K] [Fintype K] {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) : θ ≠ 0 := by
  have hord : 0 < orderOf θ := ordPos hθ
  rintro rfl
  simp at hord

private theorem finOrder {K : Type*} [Field K] [Fintype K] {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) : IsOfFinOrder θ :=
  orderOf_pos_iff.mp (ordPos hθ)

private theorem beta_not_mem_range {F K : Type*} [Field F] [Field K] [Algebra F K]
    {h : ℕ} (hh : 2 ≤ h) {θ : K} {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    θ ^ b ∉ Set.range (algebraMap F K) := fun hx => by
  have h1 := minpoly.natDegree_eq_one_iff.mpr hx
  omega

private theorem beta_add_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    {h : ℕ} (hh : 2 ≤ h) {θ : K} {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (v : F) :
    θ ^ b + algebraMap F K v ≠ 0 := by
  intro hzero
  apply beta_not_mem_range hh hb
  refine ⟨-v, ?_⟩
  rw [map_neg]
  linear_combination -hzero

private theorem exists_pow_of_order {K : Type*} [Field K]
    [Fintype K] {θ c : K} (hc : c ≠ 0) (hθ₀ : θ ≠ 0)
    (hθ : orderOf θ = Fintype.card K - 1) : ∃ k : ℕ, θ ^ k = c := by
  classical
  let g := Units.mk0 θ hθ₀
  have hg : Subgroup.zpowers g = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, ← orderOf_units, Nat.card_eq_fintype_card, Fintype.card_units]
    exact hθ
  have hmem : Units.mk0 c hc ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers, hg]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, congrArg Units.val hk⟩

private theorem theta_pow_inj {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) :
    Function.Injective (fun a : ZMod (Fintype.card F ^ h - 1) => θ ^ a.val) := by
  have _ne : NeZero (Fintype.card F ^ h - 1) := neZeroM (F := F) hh
  intro a c hac
  have hfin : IsOfFinOrder θ := finOrder hθ
  have hmod : a.val ≡ c.val [MOD orderOf θ] := (hfin.pow_eq_pow_iff_modEq).mp hac
  rw [orderM hK hθ] at hmod
  have hva : a.val < Fintype.card F ^ h - 1 := ZMod.val_lt a
  have hvc : c.val < Fintype.card F ^ h - 1 := ZMod.val_lt c
  have hval : a.val = c.val := hmod.eq_of_lt_of_lt hva hvc
  exact (ZMod.val_injective _) hval

private theorem foldl_add {M : ℕ} (t : List (ZMod M)) (a : ZMod M) :
    t.foldl (· + ·) a = a + t.sum := by
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
      simp only [List.foldl_cons, List.sum_cons]
      rw [ih]
      ac_rfl

private theorem sumNE_eq_sum {M : ℕ} (l : List (ZMod M)) (e : l ≠ []) :
    AdditiveCombinatorics.sumNE l e = l.sum := by
  cases l with
  | nil => exact False.elim (e rfl)
  | cons a t =>
      rw [List.sum_cons]
      exact foldl_add t a

private theorem pow_list_sum {K : Type*} [Field K] (θ : K) (l : List ℕ) :
    θ ^ l.sum = (l.map (θ ^ ·)).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.sum_cons, List.map_cons, List.prod_cons, pow_add, ih]

private theorem list_sum_eq_cast {M : ℕ} [NeZero M] (l : List (ZMod M)) :
    l.sum = (((l.map ZMod.val).sum : ℕ) : ZMod M) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih, ZMod.natCast_zmod_val]

private theorem theta_pow_sum_eq {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1)
    {l₁ l₂ : List (ZMod (Fintype.card F ^ h - 1))} (hsum : l₁.sum = l₂.sum) :
    θ ^ (l₁.map ZMod.val).sum = θ ^ (l₂.map ZMod.val).sum := by
  have _ne : NeZero (Fintype.card F ^ h - 1) := neZeroM hh
  have e1 : l₁.sum = ((((l₁.map ZMod.val).sum : ℕ)) : ZMod _) :=
    list_sum_eq_cast l₁
  have e2 : l₂.sum = ((((l₂.map ZMod.val).sum : ℕ)) : ZMod _) :=
    list_sum_eq_cast l₂
  rw [e1, e2] at hsum
  have hmod : (l₁.map ZMod.val).sum ≡ (l₂.map ZMod.val).sum
      [MOD Fintype.card F ^ h - 1] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hsum
  have hfin : IsOfFinOrder θ := finOrder hθ
  have hord : orderOf θ = Fintype.card F ^ h - 1 := orderM hK hθ
  apply (hfin.pow_eq_pow_iff_modEq).mpr
  rw [hord]
  exact hmod

private theorem pow_mod_eq {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) (k : ℕ) :
    θ ^ (k % (Fintype.card F ^ h - 1)) = θ ^ k := by
  have hfin : IsOfFinOrder θ := finOrder hθ
  have hmod : k % (Fintype.card F ^ h - 1) ≡ k [MOD orderOf θ] := by
    rw [orderM hK hθ]
    exact Nat.mod_modEq k _
  exact (hfin.pow_eq_pow_iff_modEq).mpr hmod

private theorem exists_bose {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (v : F) :
    ∃ a : ZMod (Fintype.card F ^ h - 1), θ ^ a.val = θ ^ b + algebraMap F K v := by
  have _ne : NeZero (Fintype.card F ^ h - 1) := neZeroM hh
  have hθ₀ : θ ≠ 0 := theta_ne_zero hθ
  have hne : θ ^ b + algebraMap F K v ≠ 0 := beta_add_ne_zero hh hb v
  obtain ⟨k, hk⟩ := exists_pow_of_order hne hθ₀ hθ
  refine ⟨(k : ZMod _), ?_⟩
  rw [ZMod.val_natCast]
  rw [pow_mod_eq hK hθ k, hk]

private noncomputable def boseFun {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (v : F) :
    ZMod (Fintype.card F ^ h - 1) :=
  Classical.choose (exists_bose hh hK hθ hb v)

private theorem boseFun_spec {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (v : F) :
    θ ^ (boseFun hh hK hθ hb v).val = θ ^ b + algebraMap F K v :=
  Classical.choose_spec (exists_bose hh hK hθ hb v)

private noncomputable def boseChoice {F K : Type*} [Field F] [Fintype F] [Field K]
    [Algebra F K] (h : ℕ) (θ : K) (b : ℕ) (a : ZMod (Fintype.card F ^ h - 1)) : F :=
  haveI := Classical.propDecidable (a ∈ boseSet F h θ b)
  if hmem : a ∈ boseSet F h θ b then Classical.choose hmem else 0

private theorem boseChoice_spec {F K : Type*} [Field F] [Fintype F] [Field K]
    [Algebra F K] (h : ℕ) (θ : K) (b : ℕ) (a : ZMod (Fintype.card F ^ h - 1))
    (hmem : a ∈ boseSet F h θ b) :
    θ ^ a.val = θ ^ b + algebraMap F K (boseChoice h θ b a) := by
  unfold boseChoice
  simp only [dite_eq_left hmem]
  exact Classical.choose_spec hmem

private theorem boseFun_injective {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    Function.Injective (boseFun hh hK hθ hb) := by
  intro v₁ v₂ heq
  have h1 := boseFun_spec hh hK hθ hb v₁
  have h2 := boseFun_spec hh hK hθ hb v₂
  rw [heq] at h1
  have heq' : θ ^ b + algebraMap F K v₁ = θ ^ b + algebraMap F K v₂ :=
    h1.symm.trans h2
  have halg : algebraMap F K v₁ = algebraMap F K v₂ := add_left_cancel_iff.mp heq'
  exact FaithfulSMul.algebraMap_injective F K halg

private theorem bose_range {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    boseSet F h θ b = Set.range (boseFun hh hK hθ hb) := by
  ext a
  constructor
  · intro hmem
    have hmem' : ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v := hmem
    obtain ⟨v, hv⟩ := hmem'
    have hspec := boseFun_spec hh hK hθ hb v
    have heq : θ ^ a.val = θ ^ (boseFun hh hK hθ hb v).val := by
      rw [hv, hspec]
    have hinj := theta_pow_inj hh hK hθ
    have ha : a = boseFun hh hK hθ hb v := hinj heq
    exact ⟨v, ha.symm⟩
  · intro hmem
    obtain ⟨v, rfl⟩ := hmem
    exact ⟨v, boseFun_spec hh hK hθ hb v⟩

private theorem bose_ncard {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    (boseSet F h θ b).ncard = Fintype.card F := by
  rw [bose_range hh hK hθ hb, ← Set.image_univ]
  rw [Set.ncard_image_of_injective _ (boseFun_injective hh hK hθ hb)]
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]

private theorem bose_nonempty {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    (boseSet F h θ b).Nonempty := by
  rw [bose_range hh hK hθ hb]
  exact ⟨_, ⟨0, rfl⟩⟩

private theorem monic_prod {F : Type*} [Field F] (l : List F) :
    ((l.map fun v => Polynomial.X + Polynomial.C v).prod).Monic := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact Polynomial.monic_one
  | cons v t ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Polynomial.Monic.mul (Polynomial.monic_X_add_C v) ih

private theorem natDegree_prod {F : Type*} [Field F] (l : List F) :
    ((l.map fun v => Polynomial.X + Polynomial.C v).prod).natDegree = l.length := by
  induction l with
  | nil => simp
  | cons v t ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_add_C v) (monic_prod t)]
      rw [Polynomial.natDegree_X_add_C, ih]
      ac_rfl

private theorem roots_prod {F : Type*} [Field F] (l : List F) :
    ((l.map fun v => Polynomial.X + Polynomial.C v).prod).roots =
      ↑(l.map Neg.neg) := by
  induction l with
  | nil => simp
  | cons v t ih =>
      simp only [List.map_cons, List.prod_cons, List.map_cons]
      have hne : (Polynomial.X + Polynomial.C v) *
          (t.map fun v => Polynomial.X + Polynomial.C v).prod ≠ 0 := by
        apply mul_ne_zero
        · exact (Polynomial.monic_X_add_C v).ne_zero
        · exact (monic_prod t).ne_zero
      rw [Polynomial.roots_mul hne, Polynomial.roots_X_add_C, ih]
      simp

private theorem aeval_prod {F K : Type*} [Field F] [Field K] [Algebra F K] (β : K)
    (l : List F) :
    (Polynomial.aeval β) ((l.map fun v => Polynomial.X + Polynomial.C v).prod) =
      (l.map fun v => β + algebraMap F K v).prod := by
  rw [map_list_prod]
  have hmap : ((l.map fun v => Polynomial.X + Polynomial.C v).map (Polynomial.aeval β)) =
      l.map fun v => β + algebraMap F K v := by
    rw [List.map_map]
    apply List.map_congr_left
    intro v _
    simp only [Function.comp_apply]
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [hmap]

private theorem poly_eq {F K : Type*} [Field F] [Field K] [Algebra F K]
    {h : ℕ} (hh : 2 ≤ h) {β : K} (hb : (minpoly F β).natDegree = h)
    {P₁ P₂ : Polynomial F}
    (hmono₁ : P₁.Monic) (hdeg₁ : P₁.natDegree = h)
    (hmono₂ : P₂.Monic) (hdeg₂ : P₂.natDegree = h)
    (haeval : (Polynomial.aeval β) P₁ = (Polynomial.aeval β) P₂) :
    P₁ = P₂ := by
  have hsub : (Polynomial.aeval β) (P₁ - P₂) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact haeval
  have hdvd : minpoly F β ∣ P₁ - P₂ := minpoly.dvd F β hsub
  by_contra hne
  have hsub_ne : P₁ - P₂ ≠ 0 := sub_ne_zero.mpr hne
  have hle : (minpoly F β).natDegree ≤ (P₁ - P₂).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hsub_ne
  have hlt : (P₁ - P₂).natDegree < h := by
    apply Polynomial.IsMonicOfDegree.natDegree_sub_lt (by omega : h ≠ 0)
    · exact Polynomial.IsMonicOfDegree.mk hdeg₁ hmono₁
    · exact Polynomial.IsMonicOfDegree.mk hdeg₂ hmono₂
  omega

private theorem vl_perm_of_poly_eq {F : Type*} [Field F] {vl₁ vl₂ : List F}
    (heq : (vl₁.map fun v => Polynomial.X + Polynomial.C v).prod =
      (vl₂.map fun v => Polynomial.X + Polynomial.C v).prod) :
    vl₁.Perm vl₂ := by
  have hroots : ((vl₁.map fun v => Polynomial.X + Polynomial.C v).prod).roots =
      ((vl₂.map fun v => Polynomial.X + Polynomial.C v).prod).roots := by
    rw [heq]
  rw [roots_prod, roots_prod] at hroots
  have hperm : (vl₁.map Neg.neg).Perm (vl₂.map Neg.neg) :=
    Multiset.coe_eq_coe.mp hroots
  exact (List.map_perm_map_iff neg_injective).mp hperm

private theorem a_perm_of_vl_perm {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    {l₁ l₂ : List (ZMod (Fintype.card F ^ h - 1))}
    (hmem₁ : ∀ x ∈ l₁, x ∈ boseSet F h θ b)
    (hmem₂ : ∀ x ∈ l₂, x ∈ boseSet F h θ b)
    (hperm : (l₁.map (boseChoice h θ b)).Perm (l₂.map (boseChoice h θ b))) :
    l₁.Perm l₂ := by
  have hinj : Function.Injective (fun a : ZMod (Fintype.card F ^ h - 1) => θ ^ a.val) :=
    theta_pow_inj hh hK hθ
  apply (List.map_perm_map_iff hinj).mp
  have hmap₁ : l₁.map (fun a : ZMod (Fintype.card F ^ h - 1) => θ ^ a.val) =
      (l₁.map (boseChoice h θ b)).map (fun v => θ ^ b + algebraMap F K v) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    exact boseChoice_spec h θ b a (hmem₁ a ha)
  have hmap₂ : l₂.map (fun a : ZMod (Fintype.card F ^ h - 1) => θ ^ a.val) =
      (l₂.map (boseChoice h θ b)).map (fun v => θ ^ b + algebraMap F K v) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    exact boseChoice_spec h θ b a (hmem₂ a ha)
  rw [hmap₁, hmap₂]
  exact hperm.map _

private theorem theta_pow_eq_aeval {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {h : ℕ} {θ : K} {b : ℕ}
    {l : List (ZMod (Fintype.card F ^ h - 1))}
    (hmem : ∀ x ∈ l, x ∈ boseSet F h θ b) :
    θ ^ (l.map ZMod.val).sum =
      (Polynomial.aeval (θ ^ b))
        (((l.map (boseChoice h θ b)).map fun v => Polynomial.X + Polynomial.C v).prod) := by
  rw [aeval_prod, pow_list_sum]
  have hlist : ((l.map ZMod.val).map (θ ^ ·)) =
      ((l.map (boseChoice h θ b)).map (fun v => θ ^ b + algebraMap F K v)) := by
    have e1 : ((l.map ZMod.val).map (θ ^ ·)) = l.map (fun a => θ ^ a.val) := by
      rw [List.map_map]
      rfl
    have e2 : l.map (fun a : ZMod (Fintype.card F ^ h - 1) => θ ^ a.val) =
        ((l.map (boseChoice h θ b)).map (fun v => θ ^ b + algebraMap F K v)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact boseChoice_spec h θ b a (hmem a ha)
    exact e1.trans e2
  rw [hlist]

/-- **Bose's construction of $B_h$-sets.** Let $h \ge 2$, let $F$ be a finite field with $q$
elements, let $K$ be a field extension of $F$ of degree $h$, let $\theta$ be a generator of the
multiplicative group $K^\times$, and let $b$ be a natural number such that $\theta^b$ has degree
$h$ over $F$. Then the generalized Bose set $\mathrm{Bose}_h(q, b)$, a subset of
$\mathbb{Z}/(q^h - 1)\mathbb{Z}$, is a $B_h$-set with exactly $q$ elements.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 3 (first sentence) (`jis-2024-24.1.2-thm-3`). -/
public theorem isBhSet_boseSet {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    AdditiveCombinatorics.IsBhSet (boseSet F h θ b) h ∧
      (boseSet F h θ b).ncard = Fintype.card F := by
  refine ⟨⟨bose_nonempty hh hK hθ hb, by omega, ?_⟩, bose_ncard hh hK hθ hb⟩
  intro l₁ l₂ hmem₁ hmem₂ len₁ len₂ e₁ e₂ hsumNE
  have hsum : l₁.sum = l₂.sum := by
    rw [← sumNE_eq_sum l₁ e₁, ← sumNE_eq_sum l₂ e₂]
    exact hsumNE
  have hpow : θ ^ (l₁.map ZMod.val).sum = θ ^ (l₂.map ZMod.val).sum :=
    theta_pow_sum_eq hh hK hθ hsum
  have haeval₁ := theta_pow_eq_aeval hmem₁
  have haeval₂ := theta_pow_eq_aeval hmem₂
  have haeval : (Polynomial.aeval (θ ^ b))
      (((l₁.map (boseChoice h θ b)).map fun v => Polynomial.X + Polynomial.C v).prod) =
      (Polynomial.aeval (θ ^ b))
        (((l₂.map (boseChoice h θ b)).map fun v => Polynomial.X + Polynomial.C v).prod) :=
    haeval₁.symm.trans (hpow.trans haeval₂)
  have hdeg₁ : (((l₁.map (boseChoice h θ b)).map fun v => Polynomial.X + Polynomial.C v).prod).natDegree = h := by
    rw [natDegree_prod, List.length_map, len₁]
  have hdeg₂ : (((l₂.map (boseChoice h θ b)).map fun v => Polynomial.X + Polynomial.C v).prod).natDegree = h := by
    rw [natDegree_prod, List.length_map, len₂]
  have hPeq := poly_eq hh hb (monic_prod _) hdeg₁ (monic_prod _) hdeg₂ haeval
  have hvlPerm : (l₁.map (boseChoice h θ b)).Perm (l₂.map (boseChoice h θ b)) :=
    vl_perm_of_poly_eq hPeq
  exact a_perm_of_vl_perm hh hK hθ hmem₁ hmem₂ hvlPerm

end

end MetaMathlibExt
