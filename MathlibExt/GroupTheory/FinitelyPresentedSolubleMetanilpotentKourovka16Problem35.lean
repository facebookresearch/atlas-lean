/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic.Group

/-!
# Metanilpotent-by-finite finitely presented soluble groups (Kourovka Notebook Problem 16.35)

Kourovka Notebook, Archive of Solved Problems, Problem 16.35 (J. R. J. Groves): is every finitely
presented soluble group nilpotent-by-nilpotent-by-finite?
Bludov’s presentation at the prime two gives a counterexample.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.35 (J. R. J.
Groves). UnsolvedMath record UM-00701227 (`KOU-16.35`), dataset ulamai/UnsolvedMath v1.8.0.

(Nilpotent-by-nilpotent)-by-finite: some normal subgroup `M` of finite index has a normal nilpotent
subgroup `N` with `M / N` nilpotent (the reading nilpotent-by-(nilpotent-by-finite) is equivalent,
by Fitting's theorem). Finitely presented is `Group.IsFinitelyPresented` and soluble is
`Group.IsSolvable`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyPresentedSolubleMetanilpotentKourovka16Problem35Wanted

/-- **Metanilpotent-by-finite groups.** A group $G$ is (nilpotent-by-nilpotent)-by-finite when it
has a normal subgroup $M$ of finite index and a normal subgroup $N$ of $M$ such that $N$ and $M/N$
are both nilpotent. -/
def IsMetanilpotentByFinite (G : Type) [Group G] : Prop :=
  ∃ M : Subgroup G, M.Normal ∧ M.FiniteIndex ∧
    ∃ N : Subgroup M, ∃ _ : N.Normal, Group.IsNilpotent N ∧ Group.IsNilpotent (M ⧸ N)

/-- **Groves's question (Kourovka 16.35).** The proposition that every finitely presented soluble
group $G$ is (nilpotent-by-nilpotent)-by-finite, that is, $G$ has a normal subgroup $M$ of finite
index and a normal subgroup $N$ of $M$ such that $N$ and $M/N$ are both nilpotent. -/
def finitelyPresentedSolubleMetanilpotentByFinite : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → Group.IsSolvable G →
    IsMetanilpotentByFinite G

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

-- Compute the derived series inside the ambient group.
private def derived (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅derived H n, derived H n⁆

private theorem derived_mono {H K : Subgroup G} (h : H ≤ K) (n : ℕ) :
    derived H n ≤ derived K n := by
  induction n with
  | zero => exact h
  | succ n ih => exact commutator_mono ih ih

private theorem derived_map {F : Type*} [Group F] (φ : G →* F) (H : Subgroup G) (n : ℕ) :
    derived (H.map φ) n = (derived H n).map φ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [derived, derived, ih, map_commutator]

private theorem derived_union (H : ℕ → Subgroup G) (h : Monotone H) (n : ℕ) :
    derived (⨆ i, H i) n = ⨆ i, derived (H i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : Monotone (fun i => derived (H i) n) := fun _ _ hij => derived_mono (h hij) n
    apply le_antisymm
    · rw [derived, ih, commutator_le]
      intro x hx y hy
      obtain ⟨i, hi⟩ := (mem_iSup_of_directed hm.directed_le).mp hx
      obtain ⟨j, hj⟩ := (mem_iSup_of_directed hm.directed_le).mp hy
      exact le_iSup (fun i => derived (H i) (n + 1)) (max i j)
        (commutator_mem_commutator (hm (le_max_left i j) hi) (hm (le_max_right i j) hj))
    · exact iSup_le fun i => derived_mono (le_iSup H i) _

private theorem derived_tail (H : Subgroup G) (n : ℕ) :
    derived H (n + 1) = derived ⁅H, H⁆ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ⁅derived H (n + 1), derived H (n + 1)⁆ = _
    rw [ih]
    rfl

-- The conjugates of H form an ascending union. Adjoining t gives a cyclic
-- quotient by that union.
private theorem ascending (H : Subgroup G) (t : G)
    (ht : H.map (MulAut.conj t) ≤ H) {n : ℕ} (hH : derived H n = ⊥) :
    derived (H ⊔ zpowers t) (n + 1) = ⊥ := by
  let S := H ⊔ zpowers t
  let stage (k : ℕ) : Subgroup G := H.map (MulAut.conj ((t ^ k)⁻¹))
  have hm : Monotone stage := monotone_nat_of_le_succ fun k x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨MulAut.conj t y, ht (mem_map_of_mem _ hy), ?_⟩
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, pow_succ', mul_inv_rev, inv_inv]
    group
  -- The derived length bound on H also holds on its ascending union of conjugates.
  let J := ⨆ k, stage k
  have hJ : derived J n = ⊥ := by
    rw [show J = ⨆ k, stage k from rfl, derived_union stage hm]
    simp only [stage, derived_map, hH, Subgroup.map_bot, iSup_bot]
  have hHJ : H ≤ J := by
    intro x hx
    exact le_iSup stage 0 ⟨x, hx, by simp⟩
  have htJ : t ∈ normalizer J := by
    apply mem_normalizer_iff''.mpr
    intro x
    simp only [J, mem_iSup_of_directed hm.directed_le]
    constructor
    · rintro ⟨k, y, hy, rfl⟩
      exact ⟨k + 1, y, hy, by simp [pow_succ, mul_assoc]⟩
    · rintro ⟨k, hk⟩
      obtain ⟨y, hy, he⟩ := hm (Nat.le_succ k) hk
      refine ⟨k, y, hy, ?_⟩
      apply_fun MulAut.conj t at he
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, pow_succ, mul_inv_rev, inv_inv] at he ⊢
      group at he
      simpa only [zpow_neg, zpow_natCast] using he
  have hS : S ≤ normalizer J := sup_le (hHJ.trans J.le_normalizer) (zpowers_le.mpr htJ)
  let N := J.subgroupOf S
  have hn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hS
  have hHS : H ≤ S := le_sup_left
  have hZS : zpowers t ≤ S := le_sup_right
  let u : S := ⟨t, hZS (mem_zpowers t)⟩
  have hJS : J ≤ S := iSup_le fun k => by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv] using
      S.mul_mem (S.mul_mem (S.inv_mem (S.pow_mem u.2 k)) (hHS hy)) (S.pow_mem u.2 k)
  have htop : N ⊔ zpowers u = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top, range_subtype]
    change (J.subgroupOf S).map S.subtype ⊔ zpowers t = S
    rw [map_subgroupOf_eq_of_le hJS]
    exact le_antisymm (sup_le hJS le_sup_right) (sup_le (hHJ.trans le_sup_left) le_sup_right)
  -- S/J is generated by the image of t.
  have hder := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop
  have hle : ⁅S, S⁆ ≤ J := by
    rw [← Subgroup.map_subtype_commutator]
    exact (map_mono hder).trans (map_subgroupOf_eq_of_le hJS).le
  rw [derived_tail]
  exact eq_bot_iff.mpr ((derived_mono hle n).trans hJ.le)

private theorem commute_endpoints {x y z w : G} (h : Commute (x * y) (z * w))
    (hyz : Commute y z) (hyw : Commute y w) (hxz : Commute x z) : Commute x w := by
  have h₁ : Commute x (z * w) := by
    simpa using h.mul_left (hyz.mul_right hyw).inv_left
  simpa using hxz.inv_right.mul_right h₁

-- Translates of d by nonnegative powers of b.
private def translate (b d : G) (i : ℕ) := MulAut.conj (b ^ i) d

private theorem step_translate (b d : G) (i : ℕ) :
    MulAut.conj b (translate b d i) = translate b d (i + 1) := by
  simp only [translate, MulAut.conj_apply, pow_succ' b, mul_inv_rev, mul_assoc]

private theorem translate_product (b c d : G) (hbc : Commute b c)
    (hcd : MulAut.conj c d = d * MulAut.conj b d) (i : ℕ) :
    MulAut.conj c (translate b d i) = translate b d i * translate b d (i + 1) := by
  have hc : Commute (MulAut.conj c) (MulAut.conj (b ^ i)) := (hbc.symm.pow_right i).map _
  change ((MulAut.conj c * MulAut.conj (b ^ i)) : MulAut G) d = _
  rw [hc.eq]
  change MulAut.conj (b ^ i) (MulAut.conj c d) = _
  rw [hcd, map_mul]
  congr 1
  simp only [translate, MulAut.conj_apply, pow_succ, mul_inv_rev, mul_assoc]

private theorem translates_commute (b c d : G) (hbc : Commute b c)
    (hcd : MulAut.conj c d = d * MulAut.conj b d) (hdd : Commute d (MulAut.conj b d))
    (i j : ℕ) : Commute (translate b d i) (translate b d j) := by
  -- Conjugating two commuting translates by c gives two commuting products
  -- of adjacent translates. Cancelling the interior factors increases the gap by one.
  let f := translate b d
  have sep (k : ℕ) : ∀ i, Commute (f i) (f (i + k)) := by
    induction k using Nat.twoStepInduction with
    | zero => simp [Commute.refl]
    | one =>
      intro i
      simpa only [f, translate, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulAut.conj_apply, pow_succ, mul_inv_rev, mul_assoc] using
        hdd.map (MulAut.conj (b ^ i)).toMonoidHom
    | more k hk hk₁ =>
      intro i
      have h := (hk₁ i).map (MulAut.conj c).toMonoidHom
      simp only [f, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        translate_product b c d hbc hcd] at h
      apply commute_endpoints h
      · convert hk (i + 1) using 2
        omega
      · convert hk₁ (i + 1) using 2
        omega
      · exact hk₁ i
  rcases le_total i j with h | h
  · simpa [Nat.add_sub_of_le h] using sep (j - i) i
  · simpa [Nat.add_sub_of_le h] using (sep (i - j) j).symm

-- Each pair specifies a relator lhs * rhs⁻¹. The first three generators are
-- the inverses of a, b, c in the Notebook's right-conjugation convention.
private def equations (a b c d : G) : Fin 7 → G × G :=
  ![(MulAut.conj a b, b ^ 2), (MulAut.conj a c, c ^ 2), (MulAut.conj a d, d),
    (b * c, c * b), (MulAut.conj c d, d * MulAut.conj b d),
    (d * MulAut.conj b d, MulAut.conj b d * d), (d ^ 2, 1)]

private theorem map_equations {F : Type*} [Group F] (φ : G →* F) (a b c d : G) (i : Fin 7) :
    Prod.map φ φ (equations a b c d i) = equations (φ a) (φ b) (φ c) (φ d) i := by
  fin_cases i <;> simp [equations, MulAut.conj_apply]

private abbrev words := equations (FreeGroup.of (0 : Fin 4)) (FreeGroup.of 1)
  (FreeGroup.of 2) (FreeGroup.of 3)

private def relators : Set (FreeGroup (Fin 4)) :=
  Set.range fun i => (words i).1 * (words i).2⁻¹

private abbrev Bludov := PresentedGroup relators
private abbrev gen (i : Fin 4) : Bludov := PresentedGroup.of i

private theorem gen_equations (i : Fin 7) :
    (equations (gen 0) (gen 1) (gen 2) (gen 3) i).1 =
      (equations (gen 0) (gen 1) (gen 2) (gen 3) i).2 := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators) (Set.mem_range_self i)
  change PresentedGroup.mk relators (words i).1 = PresentedGroup.mk relators (words i).2 at h
  have he := map_equations (PresentedGroup.mk relators) (FreeGroup.of (0 : Fin 4))
    (FreeGroup.of 1) (FreeGroup.of 2) (FreeGroup.of 3) i
  exact (congrArg Prod.fst he).symm.trans (h.trans (congrArg Prod.snd he))

private theorem bludov_solvable : Group.IsSolvable Bludov := by
  let a := gen 0
  let b := gen 1
  let c := gen 2
  let d := gen 3
  have hab : MulAut.conj a b = b ^ 2 := gen_equations 0
  have hac : MulAut.conj a c = c ^ 2 := gen_equations 1
  have had : MulAut.conj a d = d := gen_equations 2
  have hbc : Commute b c := gen_equations 3
  have hcd : MulAut.conj c d = d * MulAut.conj b d := gen_equations 4
  have hdd : Commute d (MulAut.conj b d) := gen_equations 5
  let P := closure (Set.range (translate b d))
  have hp (i : ℕ) : translate b d i ∈ P := subset_closure (Set.mem_range_self i)
  have hP : derived P 1 = ⊥ := by
    apply commutator_self_eq_bot_iff.mpr
    apply isMulCommutative_closure
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact translates_commute b c d hbc hcd hdd i j
  have hbP : P.map (MulAut.conj b) ≤ P := by
    apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change MulAut.conj b (translate b d i) ∈ P
    rw [step_translate]
    exact hp _
  have hcP : P.map (MulAut.conj c) ≤ P := by
    apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change MulAut.conj c (translate b d i) ∈ P
    rw [translate_product b c d hbc hcd]
    exact P.mul_mem (hp i) (hp (i + 1))
  have haP : P.map (MulAut.conj a) ≤ P := by
    apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change MulAut.conj a (b ^ i * d * (b ^ i)⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv, map_pow, hab, had, ← pow_mul]
    exact hp (2 * i)
  let B := P ⊔ zpowers b
  let C := B ⊔ zpowers c
  let T := C ⊔ zpowers a
  have hPB : P ≤ B := le_sup_left
  have hbB : b ∈ B := (show zpowers b ≤ B from le_sup_right) (mem_zpowers b)
  have hBC : B ≤ C := le_sup_left
  have hcC : c ∈ C := (show zpowers c ≤ C from le_sup_right) (mem_zpowers c)
  have hcB : B.map (MulAut.conj c) ≤ B := by
    rw [show B = P ⊔ zpowers b from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (hcP.trans hPB) (zpowers_le.mpr ?_)
    simpa only [MonoidHom.coe_ofClass, MulAut.conj_apply, hbc.symm.eq, mul_inv_cancel_right]
      using hbB
  have haB : B.map (MulAut.conj a) ≤ B := by
    rw [show B = P ⊔ zpowers b from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact sup_le (haP.trans hPB) (zpowers_le.mpr (show MulAut.conj a b ∈ B by
      rw [hab]; exact B.pow_mem hbB 2))
  have haC : C.map (MulAut.conj a) ≤ C := by
    rw [show C = B ⊔ zpowers c from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact sup_le (haB.trans hBC) (zpowers_le.mpr (show MulAut.conj a c ∈ C by
      rw [hac]; exact C.pow_mem hcC 2))
  have hCT : C ≤ T := le_sup_left
  have htop : T = ⊤ := eq_top_iff.mpr fun x _ => PresentedGroup.generated_by relators T (by
    intro i
    fin_cases i
    · exact (show zpowers a ≤ T from le_sup_right) (mem_zpowers a)
    · exact hCT (hBC hbB)
    · exact hCT hcC
    · exact hCT (hBC (hPB (by simpa [translate] using hp 0)))) x
  have hT : derived T 4 = ⊥ := ascending C a haC (ascending B c hcB (ascending P b hbP hP))
  refine ⟨4, ?_⟩
  change derived ⊤ 4 = ⊥
  rwa [← htop]

noncomputable section

private abbrev F := RatFunc (ZMod 2)
private theorem ratChar : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

attribute [local instance] ratChar

private abbrev K := PerfectClosure F 2
private def parameter : K := PerfectClosure.of F 2 RatFunc.X

private theorem parameter_pow_ne {n : ℕ} (hn : 0 < n) : parameter ^ n ≠ 1 := by
  intro h
  have e : (RatFunc.X : F) ^ n = 1 := (PerfectClosure.of F 2).injective (by
    simpa only [map_pow, map_one, parameter] using h)
  exact (RatFunc.transcendental_X (K := ZMod 2)).pow hn (e ▸ isAlgebraic_one)

private theorem parameter_ne_zero : parameter ≠ 0 :=
  (map_ne_zero (PerfectClosure.of F 2)).mpr RatFunc.X_ne_zero

private theorem parameter_add_ne_zero : parameter + 1 ≠ 0 := by
  intro h
  exact parameter_pow_ne (show 0 < 1 by decide) (by
    simpa only [pow_one, CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h)

private abbrev frob : Equiv.Perm K := (frobeniusEquiv K 2).toEquiv
private abbrev scale (r : K) (h : r ≠ 0) : Equiv.Perm K := Equiv.mulLeft₀ r h
private abbrev shift (v : K) : Equiv.Perm K := Equiv.addLeft v

private theorem conj_scale (r : K) (hr : r ≠ 0) :
    MulAut.conj frob (scale r hr) = scale r hr ^ 2 := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  ext x
  change (r * x) ^ 2 = r * (r * x ^ 2)
  ring

private theorem conj_shift (r v : K) (hr : r ≠ 0) :
    MulAut.conj (scale r hr) (shift v) = shift (r * v) := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  ext x
  change r * (v + x) = r * v + r * x
  exact mul_add _ _ _

-- Frobenius, multiplication by X and X+1, and translation by 1.
private abbrev permGen : Fin 4 → Equiv.Perm K := ![frob, scale parameter parameter_ne_zero,
  scale (parameter + 1) parameter_add_ne_zero, shift 1]

private theorem perm_equations (i : Fin 7) :
    (equations (permGen 0) (permGen 1) (permGen 2) (permGen 3) i).1 =
    (equations (permGen 0) (permGen 1) (permGen 2) (permGen 3) i).2 := by
  fin_cases i
  · exact conj_scale _ _
  · exact conj_scale _ _
  · change MulAut.conj frob (shift 1) = shift 1
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    ext x
    change (1 + x) ^ 2 = 1 + x ^ 2
    exact (CharTwo.add_sq 1 x).trans (by rw [one_pow])
  · ext x
    change parameter * ((parameter + 1) * x) = (parameter + 1) * (parameter * x)
    ring
  · change MulAut.conj (scale _ _) (shift _) = shift _ * MulAut.conj (scale _ _) (shift _)
    rw [conj_shift, conj_shift]
    ext x
    change (parameter + 1) * 1 + x = 1 + (parameter * 1 + x)
    ring
  · change shift _ * MulAut.conj (scale _ _) (shift _) =
      MulAut.conj (scale _ _) (shift _) * shift _
    rw [conj_shift]
    ext x
    change 1 + (parameter * 1 + x) = parameter * 1 + (1 + x)
    abel
  · ext x
    change 1 + (1 + x) = x
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private def action : Bludov →* Equiv.Perm K := PresentedGroup.toGroup (f := permGen) (by
  rintro _ ⟨i, rfl⟩
  rw [map_mul, map_inv, mul_inv_eq_one]
  have he := map_equations (FreeGroup.lift permGen) (FreeGroup.of (0 : Fin 4))
    (FreeGroup.of 1) (FreeGroup.of 2) (FreeGroup.of 3) i
  simp only [FreeGroup.lift_apply_of] at he
  exact (congrArg Prod.fst he).trans ((perm_equations i).trans (congrArg Prod.snd he).symm))

private theorem act_gen (i : Fin 4) : action (gen i) = permGen i := PresentedGroup.toGroup.of _

-- In a nilpotent group, repeatedly taking commutators with a fixed element
-- reaches the identity.
private def iterComm (x y : G) : ℕ → G
  | 0 => y
  | n + 1 => ⁅x, iterComm x y n⁆

private theorem map_iterComm {F' : Type*} [Group F'] (φ : G →* F') (x y : G) (n : ℕ) :
    φ (iterComm x y n) = iterComm (φ x) (φ y) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterComm, map_commutatorElement, ih, iterComm]

private theorem nil_iter (hnil : Group.IsNilpotent G) (x y : G) :
    ∃ n, iterComm x y n = 1 := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp hnil
  have hmem (k : ℕ) : iterComm x y k ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
    induction k with
    | zero => exact mem_top _
    | succ k ih =>
      rw [lowerCentralSeries_succ, commutator_comm]
      exact commutator_mem_commutator (mem_top x) ih
  exact ⟨n, mem_bot.mp (hn ▸ hmem n)⟩

private theorem comm_action (x y : Bludov) (f : K → K)
    (h : ∀ z, action x (action y z) = f (action y (action x z))) (z : K) :
    action ⁅x, y⁆ z = f z := by
  obtain ⟨w, rfl⟩ := (action y * action x).surjective z
  have he : ⁅action x, action y⁆ * (action y * action x) = action x * action y := by
    rw [commutatorElement_def]
    group
  rw [map_commutatorElement, ← Equiv.Perm.mul_apply, he]
  exact h w

-- The two kinds of nonidentity permutations detected by the action.
private def IsScaling (x : Bludov) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ z, action x z = parameter ^ k * z

private def IsTranslation (y : Bludov) : Prop :=
  ∃ v : K, v ≠ 0 ∧ ∀ z, action y z = v + z

private theorem scale_comm_shift {x y : Bludov} (hx : IsScaling x) (hy : IsTranslation y) :
    IsTranslation ⁅x, y⁆ := by
  obtain ⟨k, hk, hx⟩ := hx
  obtain ⟨v, hv, hy⟩ := hy
  refine ⟨(parameter ^ k - 1) * v, mul_ne_zero (sub_ne_zero.mpr (parameter_pow_ne hk)) hv, ?_⟩
  apply comm_action
  intro z
  simp only [hx, hy]
  ring

private theorem pos_scale_iter (m : ℕ) (hm : 0 < m) (k : ℕ) :
    IsScaling (iterComm (gen 0 ^ m) (gen 1 ^ m) k) := by
  have ha (n : ℕ) (z : K) : action (gen 0 ^ n) z = z ^ (2 ^ n) := by
    induction n generalizing z with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Equiv.Perm.mul_apply, ih, act_gen]
      change (z ^ 2) ^ (2 ^ n) = z ^ (2 ^ (n + 1))
      rw [← pow_mul, pow_succ' 2]
  induction k with
  | zero =>
    refine ⟨m, hm, ?_⟩
    change ∀ z, action (gen 1 ^ m) z = parameter ^ m * z
    intro z
    clear hm
    induction m generalizing z with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, map_mul, Equiv.Perm.mul_apply, ih, act_gen]
      change parameter ^ m * (parameter * z) = parameter ^ (m + 1) * z
      rw [pow_succ, mul_assoc]
  | succ k ih =>
    obtain ⟨l, hl, hs⟩ := ih
    have hr : 1 < 2 ^ m := one_lt_pow₀ (by decide) hm.ne'
    refine ⟨l * (2 ^ m - 1), Nat.mul_pos hl (by omega), ?_⟩
    apply comm_action
    intro z
    simp only [ha, hs, mul_pow]
    rw [← mul_assoc, ← pow_add, ← pow_mul, ← Nat.mul_succ, Nat.succ_eq_add_one,
      Nat.sub_add_cancel hr.le]

private theorem not_metanilpotent
    (M : Subgroup Bludov) [M.Normal] [M.FiniteIndex] (N : Subgroup M) [N.Normal]
    (hN : Group.IsNilpotent N) (hQ : Group.IsNilpotent (M ⧸ N)) : False := by
  let m := M.index
  let a : M := ⟨gen 0 ^ m, M.pow_index_mem _⟩
  let b : M := ⟨gen 1 ^ m, M.pow_index_mem _⟩
  let q := QuotientGroup.mk' N
  obtain ⟨k, hk⟩ := nil_iter hQ (q a) (q b)
  -- Nilpotence of M/N puts an element acting by a nontrivial scaling in N.
  let x : M := iterComm a b k
  have hx : x ∈ N := (QuotientGroup.eq_one_iff _).mp ((map_iterComm q a b k).trans hk)
  have hscale : IsScaling (x : Bludov) := by
    change IsScaling (M.subtype (iterComm a b k))
    rw [map_iterComm]
    exact pos_scale_iter m M.index_pos k
  let d := gen 3
  have hd : IsTranslation d := ⟨1, one_ne_zero, fun z => by
    rw [show d = gen 3 from rfl, act_gen]
    rfl⟩
  -- Two commutators put a nonzero translation in N, first using normality of M,
  -- then normality of N in M. Further commutators with x keep the translation nonzero.
  let y : M := ⟨⁅(x : Bludov), d⁆, commutator_le_left M ⊤
    (commutator_mem_commutator x.2 (mem_top d))⟩
  have hy : IsTranslation (y : Bludov) := scale_comm_shift hscale hd
  let u : N := ⟨x, hx⟩
  let v : N := ⟨⁅x, y⁆, commutator_le_left N ⊤ (commutator_mem_commutator hx (mem_top y))⟩
  let incl := M.subtype.comp N.subtype
  have hv : IsTranslation (incl v) := scale_comm_shift hscale hy
  obtain ⟨j, hj⟩ := nil_iter hN u v
  have htrans (l : ℕ) : IsTranslation (incl (iterComm u v l)) := by
    induction l with
    | zero => exact hv
    | succ l ih =>
      rw [iterComm, map_commutatorElement]
      exact scale_comm_shift hscale ih
  obtain ⟨w, hw, ew⟩ := htrans j
  apply hw
  simpa [hj] using (ew 0).symm

end

/--
**Groves's question (Kourovka 16.35) has a negative answer.** Not every finitely presented
soluble group is (nilpotent-by-nilpotent)-by-finite: there is a finitely presented soluble group
$G$ such that for no normal subgroup $M$ of finite index in $G$ is there a normal subgroup $N$ of
$M$ with $N$ and $M/N$ both nilpotent.

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.35 (J. R. J. Groves); resolution:
V. V. Bludov, letter of 27 April 2007, as recorded in the Kourovka Archive, Kourovka Archive,
Problem 16.35 (No: for a prime p, ⟨a, b, c, d | b^a = b^p, c^a = c^p, d^a = d, c^b = c, d^c = d d^b,
[d, d^b] = 1, d^p = 1⟩ is soluble of derived length 3 but not metanilpotent-by-finite).
-/
theorem finitelyPresentedSolubleMetanilpotentByFinite_refuted :
    ¬ finitelyPresentedSolubleMetanilpotentByFinite := by
  intro h
  have : Finite relators := Set.finite_range _
  obtain ⟨M, hM, hi, N, hn, hN, hQ⟩ := h Bludov inferInstance bludov_solvable
  exact not_metanilpotent M N hN hQ

end MathlibExt.GroupTheory.FinitelyPresentedSolubleMetanilpotentKourovka16Problem35Wanted
