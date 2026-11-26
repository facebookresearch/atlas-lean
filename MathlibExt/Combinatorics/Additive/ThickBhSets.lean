/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import MathlibExt.Combinatorics.Additive.BhSet
public import MathlibExt.Combinatorics.Additive.SingerSet
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.Perm.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Constructing thick `B_h`-sets: Bose's and Singer's constructions

Bose's and Singer's constructions of `B_h`-sets in cyclic groups, following Kevin O'Bryant,
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

private theorem exists_pow {K : Type*} [Field K] [Fintype K] {θ c : K}
    (hθ₀ : θ ≠ 0) (hθ : orderOf θ = Fintype.card K - 1) (hc : c ≠ 0) :
    ∃ k : ℕ, θ ^ k = c := by
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

private theorem sumNE_eq_sum {G : Type*} [AddCommMonoid G] (l : List G) (e : l ≠ []) :
    AdditiveCombinatorics.sumNE l e = l.sum := by
  cases l with
  | nil => exact (e rfl).elim
  | cons a l =>
    change l.foldl (· + ·) a = a + l.sum
    induction l generalizing a with
    | nil => simp
    | cons b l ih => simp [ih, add_assoc]

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

private theorem exists_bose {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (v : F) :
    ∃ a : ZMod (Fintype.card F ^ h - 1), θ ^ a.val = θ ^ b + algebraMap F K v := by
  have _ne : NeZero (Fintype.card F ^ h - 1) := neZeroM hh
  have hθ₀ : θ ≠ 0 := theta_ne_zero hθ
  have hne : θ ^ b + algebraMap F K v ≠ 0 := beta_add_ne_zero hh hb v
  obtain ⟨k, hk⟩ := exists_pow hθ₀ hθ hne
  refine ⟨(k : ZMod _), ?_⟩
  rw [ZMod.val_natCast, ← orderM hK hθ, pow_mod_orderOf, hk]

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

private theorem prod_X_add_C {F : Type*} [Field F] (l : List F) :
    (l.map fun v => Polynomial.X + Polynomial.C v).prod =
      ((l.map Neg.neg : Multiset F).map fun a => Polynomial.X - Polynomial.C a).prod := by
  rw [Multiset.map_coe, Multiset.prod_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
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
  rw [prod_X_add_C, prod_X_add_C, Polynomial.roots_multiset_prod_X_sub_C,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
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
    [Algebra F K] {h : ℕ} {θ : K} {b : ℕ}
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
  have hdeg₁ : (((l₁.map (boseChoice h θ b)).map fun v =>
      Polynomial.X + Polynomial.C v).prod).natDegree = h := by
    rw [prod_X_add_C, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.coe_card,
      List.length_map, List.length_map, len₁]
  have hdeg₂ : (((l₂.map (boseChoice h θ b)).map fun v =>
      Polynomial.X + Polynomial.C v).prod).natDegree = h := by
    rw [prod_X_add_C, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.coe_card,
      List.length_map, List.length_map, len₂]
  have hmono (l : List F) : ((l.map fun v => Polynomial.X + Polynomial.C v).prod).Monic := by
    rw [prod_X_add_C]
    exact Polynomial.monic_multisetProd_X_sub_C _
  have hPeq := poly_eq hh hb (hmono _) hdeg₁ (hmono _) hdeg₂ haeval
  have hvlPerm : (l₁.map (boseChoice h θ b)).Perm (l₂.map (boseChoice h θ b)) :=
    vl_perm_of_poly_eq hPeq
  exact a_perm_of_vl_perm hh hK hθ hmem₁ hmem₂ hvlPerm

end

open Polynomial

private noncomputable def linePolynomial {F : Type*} [Field F] : Option F → F[X]
  | none => 1
  | some t => X - C t

private theorem linePolynomial_monic {F : Type*} [Field F] (t : Option F) :
    (linePolynomial t).Monic := by
  cases t <;> simp [linePolynomial, monic_X_sub_C, monic_one]

private theorem linePolynomial_degree {F : Type*} [Field F] (t : Option F) :
    (linePolynomial t).natDegree ≤ 1 := by
  cases t <;> simp [linePolynomial]

private theorem product_degree {F : Type*} [Field F] (l : List (Option F)) :
    (l.map linePolynomial).prod.natDegree ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    exact (natDegree_mul_le ..).trans (by have := linePolynomial_degree a; omega)

private theorem product_monic {F : Type*} [Field F] (l : List (Option F)) :
    (l.map linePolynomial).prod.Monic := by
  induction l with
  | nil => simp
  | cons a l ih => simpa using (linePolynomial_monic a).mul ih

private theorem product_roots {F : Type*} [Field F] (l : List (Option F)) :
    (l.map linePolynomial).prod.roots = (l.filterMap id : Multiset F) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, roots_mul
      (mul_ne_zero (linePolynomial_monic a).ne_zero (product_monic l).ne_zero), ih]
    cases a <;> simp [linePolynomial]

private theorem option_perm {F : Type*} (l₁ l₂ : List (Option F))
    (hlen : l₁.length = l₂.length)
    (hroots : (l₁.filterMap id : Multiset F) = (l₂.filterMap id : Multiset F)) :
    l₁.Perm l₂ := by
  classical
  have hcount (l : List (Option F)) (a : F) :
      l.count (some a) = (l.filterMap id).count a := by
    induction l with
    | nil => simp
    | cons b l ih =>
      cases b with
      | none => simp [ih]
      | some b =>
        by_cases h : a = b
        · subst b; simp [ih]
        · simp [ih, Ne.symm h]
  have hlength (l : List (Option F)) :
      l.length = l.count none + (l.filterMap id).length := by
    induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp [ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  have hp : (l₁.filterMap id).Perm (l₂.filterMap id) := Quotient.exact hroots
  apply List.perm_iff_count.mpr
  intro a
  cases a with
  | none => have := hp.length_eq; have := hlength l₁; have := hlength l₂; omega
  | some a => rw [hcount, hcount]; exact hp.count_eq a

private theorem polynomial_eq_of_aeval {F K : Type*} [Field F] [Field K] [Algebra F K]
    {x : K} {d : ℕ} (hx : (minpoly F x).natDegree = d + 1)
    {p q : F[X]} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (he : aeval x p = aeval x q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hn
  have hd := natDegree_le_of_dvd (minpoly.dvd F x (by simpa using sub_eq_zero.mpr he)) hn
  have hsub := natDegree_sub_le p q
  rw [hx] at hd
  omega

private theorem pow_decompose {F K : Type*} [Field F] [Field K] [Algebra F K]
    {θ : K} {ν : F} {M : ℕ} (hnorm : algebraMap F K ν = θ ^ M) (a : ℕ) :
    θ ^ a = algebraMap F K (ν ^ (a / M)) * θ ^ (a % M) := by
  rw [map_pow, hnorm, ← pow_mul, ← pow_add, Nat.div_add_mod]

private theorem pow_scale {F K : Type*} [Field F] [Field K] [Algebra F K]
    {θ : K} {ν : F} {M a b : ℕ} (hν : ν ≠ 0)
    (hnorm : algebraMap F K ν = θ ^ M) (hab : (a : ZMod M) = b) :
    ∃ c : F, c ≠ 0 ∧ θ ^ a = algebraMap F K c * θ ^ b := by
  have hm := (ZMod.natCast_eq_natCast_iff' a b M).mp hab
  refine ⟨ν ^ (a / M) / ν ^ (b / M), div_ne_zero (pow_ne_zero _ hν)
    (pow_ne_zero _ hν), ?_⟩
  rw [pow_decompose hnorm a, pow_decompose hnorm b, map_div₀, ← mul_assoc,
    div_mul_cancel₀ _ ((map_ne_zero_iff _ (algebraMap F K).injective).mpr (pow_ne_zero _ hν)), hm]

private theorem cast_eq_of_scale {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {θ : K} {M a b : ℕ}
    (hθ : orderOf θ = Fintype.card K - 1)
    (hM : M * (Fintype.card F - 1) = Fintype.card K - 1)
    {c : F} (hc : c ≠ 0) (he : θ ^ a = algebraMap F K c * θ ^ b) :
    (a : ZMod M) = b := by
  have hord : 0 < orderOf θ := by rw [hθ]; exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have hp := congrArg (fun z : K => z ^ (Fintype.card F - 1)) he
  rw [mul_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one,
    one_mul, ← pow_mul, ← pow_mul] at hp
  have hm := (orderOf_pos_iff.mp hord).pow_eq_pow_iff_modEq.mp hp
  rw [hθ, ← hM] at hm
  exact (ZMod.natCast_eq_natCast_iff a b M).mpr
    (Nat.ModEq.mul_right_cancel' (by have : 1 < Fintype.card F := Fintype.one_lt_card; omega) hm)

private theorem line_eval_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    {x : K} (hx : x ∉ (algebraMap F K).range) (t : Option F) :
    aeval x (linePolynomial t) ≠ 0 := by
  cases t with
  | none => simp [linePolynomial]
  | some t => simpa [linePolynomial, sub_eq_zero] using fun h => hx ⟨t, h.symm⟩

private theorem product_eval {F K : Type*} [Field F] [Field K] [Algebra F K]
    {θ x : K} (k : Option F → ℕ)
    (hk : ∀ t, θ ^ k t = aeval x (linePolynomial t)) (l : List (Option F)) :
    θ ^ (l.map k).sum = aeval x (l.map linePolynomial).prod := by
  induction l with
  | nil => simp
  | cons t l ih => simp [pow_add, hk, ih]

private theorem lift_list {A B : Type*} (f : A → B) (l : List B)
    (hl : ∀ a ∈ l, ∃ t, f t = a) : ∃ L : List A, L.map f = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨t, ht⟩ := hl a (by simp)
    obtain ⟨L, hL⟩ := ih (fun a ha => hl a (by simp [ha]))
    exact ⟨t :: L, by simp [ht, hL]⟩

@[expose] public section

/-- **Singer's construction of $B_h$-sets.** Let $h \ge 2$, let $F$ be a finite field with $q$
elements, let $K$ be a field extension of $F$ of degree $h + 1$, let $\theta$ be a generator of
the multiplicative group $K^\times$, and let $b$ be a natural number such that $\theta^b$ has
degree $h + 1$ over $F$. Then the generalized Singer set $\mathrm{Singer}_h(q, b)$, a subset of
$\mathbb{Z}/M\mathbb{Z}$ with $M = (q^{h+1} - 1)/(q - 1)$, is a $B_h$-set with exactly $q + 1$
elements.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 3 (second sentence) (`jis-2024-24.1.2-thm-3`). -/
public theorem isBhSet_singerSet {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h + 1) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h + 1) :
    AdditiveCombinatorics.IsBhSet (singerSet F h θ b) h ∧
      (singerSet F h θ b).ncard = Fintype.card F + 1 := by
  classical
  let q := Fintype.card F
  let M := (q ^ (h + 1) - 1) / (q - 1)
  have hq : 1 < q := Fintype.one_lt_card
  have hcard : Fintype.card K = q ^ (h + 1) := by
    rw [Module.card_eq_pow_finrank (K := F), hK]
  have hM : M * (Fintype.card F - 1) = Fintype.card K - 1 := by
    rw [hcard]
    exact Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one q (h + 1))
  have : NeZero M := ⟨(Nat.div_pos
    (Nat.sub_le_sub_right (Nat.le_pow (by omega)) 1) (by omega)).ne'⟩
  have hord : 0 < orderOf θ := by
    rw [hθ]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have hθ₀ : θ ≠ 0 := by rintro rfl; simp at hord
  have hx : θ ^ b ∉ (algebraMap F K).range := fun hx => by
    have := minpoly.natDegree_eq_one_iff.mpr hx
    omega
  let ν := Algebra.norm F θ
  have hν : ν ≠ 0 := Algebra.norm_ne_zero_iff.mpr hθ₀
  have hnorm : algebraMap F K ν = θ ^ M := by
    rw [FiniteField.algebraMap_norm_eq_pow, Module.natCard_eq_pow_finrank (K := F) (V := K),
      hK, Nat.card_eq_fintype_card]
  choose k hk using fun t : Option F => exists_pow hθ₀ hθ (line_eval_ne_zero hx t)
  let f : Option F → ZMod M := fun t => k t
  have hf : Function.Injective f := by
    intro t s hts
    obtain ⟨c, hc, he⟩ := pow_scale hν hnorm hts
    rw [hk t, hk s] at he
    have hp : linePolynomial t = C c * linePolynomial s :=
      polynomial_eq_of_aeval hb ((linePolynomial_degree t).trans (by omega))
        ((natDegree_C_mul_le c _).trans ((linePolynomial_degree s).trans (by omega)))
        (by simpa using he)
    have hr := congrArg Polynomial.roots hp
    rw [roots_C_mul _ hc] at hr
    cases t <;> cases s <;>
      simp only [linePolynomial, roots_one, Multiset.empty_eq_zero, roots_X_sub_C,
        Multiset.zero_ne_singleton, Multiset.singleton_ne_zero, Multiset.singleton_inj,
        Option.some.injEq] at hr ⊢
    exact hr
  have hmem (t : Option F) : f t ∈ singerSet F h θ b := by
    obtain ⟨c, hc, he⟩ := pow_scale hν hnorm (a := (f t).val) (b := k t)
      (ZMod.natCast_zmod_val (f t))
    rw [hk t] at he
    cases t with
    | none => exact ⟨0, c, by simpa [linePolynomial] using he⟩
    | some t =>
      refine ⟨c, -c * t, ?_⟩
      rw [he]
      simp only [linePolynomial, map_sub, aeval_X, aeval_C, map_mul, map_neg]
      ring
  have hsurj (a : ZMod M) (ha : a ∈ singerSet F h θ b) : ∃ t, f t = a := by
    obtain ⟨u, v, huv⟩ := ha
    by_cases hu : u = 0
    · subst u
      have hv : v ≠ 0 := by
        intro hv
        apply pow_ne_zero a.val hθ₀
        simpa only [hv, map_zero, zero_mul, add_zero] using huv
      refine ⟨none, ?_⟩
      have he : θ ^ a.val = algebraMap F K v * θ ^ k none := by
        simpa [hk, linePolynomial] using huv
      have heq := cast_eq_of_scale hθ hM hv he
      simpa [f] using heq.symm
    · refine ⟨some (-v / u), ?_⟩
      have he : θ ^ a.val = algebraMap F K u * θ ^ k (some (-v / u)) := by
        rw [hk, linePolynomial]
        simp only [map_sub, aeval_X, aeval_C, map_neg, map_div₀]
        rw [huv, neg_div, sub_neg_eq_add, mul_add,
          mul_comm (algebraMap F K u) (algebraMap F K v / algebraMap F K u),
          div_mul_cancel₀ _ ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hu)]
      have heq := cast_eq_of_scale hθ hM hu he
      simpa [f] using heq.symm
  have hset : singerSet F h θ b = Set.range f := by
    ext a
    exact ⟨hsurj a, fun ⟨t, ht⟩ => ht ▸ hmem t⟩
  refine ⟨⟨⟨f none, hmem none⟩, by omega, ?_⟩, ?_⟩
  · intro l₁ l₂ hl₁ hl₂ hlen₁ hlen₂ e₁ e₂ he
    obtain ⟨L₁, rfl⟩ := lift_list f l₁ (fun a ha => hsurj a (hl₁ a ha))
    obtain ⟨L₂, rfl⟩ := lift_list f l₂ (fun a ha => hsurj a (hl₂ a ha))
    have hL₁ : L₁.length = h := by simpa using hlen₁
    have hL₂ : L₂.length = h := by simpa using hlen₂
    rw [sumNE_eq_sum, sumNE_eq_sum] at he
    have hcast (L : List (Option F)) : ((L.map k).sum : ZMod M) = (L.map f).sum := by
      induction L with
      | nil => simp
      | cons t L ih => simp [f, ih]
    obtain ⟨c, hc, heval⟩ := pow_scale hν hnorm
      ((hcast L₁).trans (he.trans (hcast L₂).symm))
    rw [product_eval k hk, product_eval k hk] at heval
    have hp : (L₁.map linePolynomial).prod = C c * (L₂.map linePolynomial).prod :=
      polynomial_eq_of_aeval hb (by simpa [hL₁] using product_degree L₁)
        ((natDegree_C_mul_le c _).trans (by simpa [hL₂] using product_degree L₂))
        (by simpa using heval)
    have hr := congrArg Polynomial.roots hp
    rw [roots_C_mul _ hc, product_roots, product_roots] at hr
    exact (option_perm L₁ L₂ (hL₁.trans hL₂.symm) hr).map f
  · rw [hset, Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_option]

end

end MetaMathlibExt
