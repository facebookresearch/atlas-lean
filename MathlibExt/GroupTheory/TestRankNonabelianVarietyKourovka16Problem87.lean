/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Test ranks of relatively free groups in a nonabelian variety

The variety of groups with central commutators of exponent dividing two refutes
Timoshenko's proposed characterization of abelian varieties by test rank.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87Wanted

/-- **Groups satisfying a set of laws in countably many variables.** Let $F_\mathbb{N}$ be the free
group on countably many generators and $W \subseteq F_\mathbb{N}$ a set of words, the laws. A group
$G$ satisfies the laws $W$ when $\varphi(w) = 1$ for every $w \in W$ and every homomorphism
$\varphi \colon F_\mathbb{N} \to G$, that is, every law takes the value $1$ under every
substitution of elements of $G$ for the variables. The variety defined by $W$ is the class of
these groups. -/
def SatisfiesLaws (W : Set (FreeGroup ℕ)) (G : Type*) [Group G] : Prop :=
  ∀ w ∈ W, ∀ φ : FreeGroup ℕ →* G, φ w = 1

/-- **Verbal subgroup of a free group of finite rank.** Let $W$ be a set of laws in the free group
$F_\mathbb{N}$ on countably many generators, and let $F_r$ be the free group on $r$ generators. The
verbal subgroup $V_W(F_r)$ of $F_r$ for $W$ is the normal closure in $F_r$ of all elements
$\varphi(w)$ with $w \in W$ and $\varphi \colon F_\mathbb{N} \to F_r$ a homomorphism. -/
abbrev verbalSubgroup (W : Set (FreeGroup ℕ)) (r : ℕ) : Subgroup (FreeGroup (Fin r)) :=
  Subgroup.normalClosure {x | ∃ w ∈ W, ∃ φ : FreeGroup ℕ →* FreeGroup (Fin r), φ w = x}

/-- **Relatively free group as a quotient of a free group.** Let $W$ be a set of laws in the free
group $F_\mathbb{N}$ on countably many generators, and let $r \in \mathbb{N}$. The free
$r$-generator group $G_r$ of the variety defined by $W$ is the quotient $F_r / V_W(F_r)$ of the
free group $F_r$ on $r$ generators by its verbal subgroup $V_W(F_r)$ for $W$. -/
abbrev RelativelyFreeGroup (W : Set (FreeGroup ℕ)) (r : ℕ) : Type :=
  FreeGroup (Fin r) ⧸ verbalSubgroup W r

/-- **Test set of a group.** A subset $S$ of a group $G$ is a test set when every endomorphism of
$G$ that fixes every element of $S$ is bijective, that is, an automorphism of $G$. -/
def IsTestSet {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ f : G →* G, (∀ s ∈ S, f s = s) → Function.Bijective f

/-- **Test rank of a group.** A group $G$ has test rank $r \in \mathbb{N}$ when $G$ has a test set
of cardinality $r$ and every test set of $G$ has cardinality at least $r$ (an infinite set counting
as having cardinality $\infty$), that is, when the minimum of the cardinalities of the test sets of
$G$ is $r$. -/
def HasTestRank (G : Type*) [Group G] (r : ℕ) : Prop :=
  (∃ S : Set G, IsTestSet S ∧ S.encard = r) ∧ ∀ S : Set G, IsTestSet S → (r : ℕ∞) ≤ S.encard

/-- **Timoshenko's test rank question, part (a).** The statement that for every set $W$ of laws in
the free group $F_\mathbb{N}$ on countably many generators, if for every $r \ge 1$ the free
$r$-generator group $G_r$ of the variety defined by $W$ has test rank $r$, then this variety is
abelian: every group satisfying the laws $W$ is abelian.

This is Kourovka Notebook Problem 16.87(a) (E. I. Timoshenko), which asks whether the statement
holds. -/
def testRankVarietyAbelian : Prop :=
  ∀ W : Set (FreeGroup ℕ), (∀ r : ℕ, 1 ≤ r → HasTestRank (RelativelyFreeGroup W r) r) →
    ∀ (G : Type) [Group G], SatisfiesLaws W G → ∀ a b : G, a * b = b * a

/-- **Timoshenko's test rank question, part (b).** The statement that for every set $W$ of laws in
the free group $F_\mathbb{N}$ on countably many generators, if for every $r \ge 1$ the free
$r$-generator group $G_r$ of the variety defined by $W$ has test rank $r$ and the variety is not
periodic (there is no $n > 0$ with $g^n = 1$ for every element $g$ of every group satisfying $W$),
then the variety is the variety of all abelian groups: a group satisfies the laws $W$ if and only
if it is abelian.

This is Kourovka Notebook Problem 16.87(b) (E. I. Timoshenko), which asks whether the statement
holds. -/
def testRankNonperiodicVarietyAllAbelian : Prop :=
  ∀ W : Set (FreeGroup ℕ), (∀ r : ℕ, 1 ≤ r → HasTestRank (RelativelyFreeGroup W r) r) →
    (¬ ∃ n : ℕ, 0 < n ∧ ∀ (G : Type) [Group G], SatisfiesLaws W G → ∀ g : G, g ^ n = 1) →
      ∀ (G : Type) [Group G], (SatisfiesLaws W G ↔ ∀ a b : G, a * b = b * a)

open scoped commutatorElement
open FreeGroup (of)

private def laws : Set (FreeGroup ℕ) :=
  {⁅⁅of 0, of 1⁆, of 2⁆, ⁅of 0, of 1⁆ ^ 2}

private theorem satisfies_iff {G : Type*} [Group G] :
    SatisfiesLaws laws G ↔
      (∀ x y z : G, Commute ⁅x, y⁆ z) ∧ (∀ x y : G, ⁅x, y⁆ ^ 2 = 1) := by
  let subst (x y z : G) := FreeGroup.lift (fun | 0 => x | 1 => y | _ => z)
  constructor
  · intro h
    constructor
    · intro x y z
      have he := h _ (Set.mem_insert _ _) (subst x y z)
      simpa [subst, commutatorElement_eq_one_iff_commute] using he
    · intro x y
      have he := h _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (subst x y 1)
      simpa [subst] using he
  · rintro ⟨hc, he⟩ w (rfl | hw) φ
    · simp [commutatorElement_eq_one_iff_commute, hc]
    · obtain rfl : w = _ := hw
      simpa using he (φ (of 0)) (φ (of 1))

private theorem quotient_satisfies (W : Set (FreeGroup ℕ)) (r : ℕ) :
    SatisfiesLaws W (RelativelyFreeGroup W r) := by
  intro w hw φ
  let q := QuotientGroup.mk' (verbalSubgroup W r)
  choose x hx using fun i : ℕ => QuotientGroup.mk'_surjective (verbalSubgroup W r) (φ (of i))
  have hφ : q.comp (FreeGroup.lift x) = φ := by
    ext i
    simpa [q] using hx i
  rw [← hφ]
  exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨w, hw, _, rfl⟩)

private abbrev Free (r : ℕ) := RelativelyFreeGroup laws r

private def gen {r : ℕ} (i : Fin r) : Free r :=
  QuotientGroup.mk' (verbalSubgroup laws r) (of i)

private theorem gen_isTestSet (r : ℕ) : IsTestSet (Set.range (@gen r)) := by
  intro f hf
  have h : f = MonoidHom.id _ := by
    ext i
    exact hf _ ⟨i, rfl⟩
  rw [h]
  exact Function.bijective_id

/-- The vector of exponent sums descends through both commutator laws. -/
private def exponents (r : ℕ) : Free r →* Multiplicative (Fin r → ℤ) :=
  let e := FreeGroup.lift (fun i : Fin r => Multiplicative.ofAdd (Pi.single i (1 : ℤ)))
  QuotientGroup.lift _ e (Subgroup.normalClosure_le_normal (by
    rintro _ ⟨w, hw, φ, rfl⟩
    have h : SatisfiesLaws laws (Multiplicative (Fin r → ℤ)) :=
      satisfies_iff.2 ⟨fun _ _ _ => Commute.all .., fun _ _ => by
        rw [(Commute.all ..).commutator_eq, one_pow]⟩
    exact h w hw (e.comp φ)))

private theorem exponents_gen {r : ℕ} (i : Fin r) :
    (exponents r (gen i)).toAdd = Pi.single i 1 := by
  simp [exponents, gen]

-- A character vanishing on a test set is zero when all squares are central.
private theorem character_zero {G : Type*} [Group G] (hc : ∀ x y : G, Commute (x ^ 2) y)
    {S : Set G} (hS : IsTestSet S) (χ : G →* Multiplicative ℤ)
    (hχ : ∀ s ∈ S, (χ s).toAdd = 0) (g : G) : (χ g).toAdd = 0 := by
  have nonpos (x : G) : (χ x).toAdd ≤ 0 := by
    by_contra! hx
    -- The central factor is trivial on S, so this endomorphism fixes S pointwise.
    let f : G →* G :=
      { toFun := fun y => y * (x ^ 2) ^ (χ y).toAdd
        map_one' := by simp
        map_mul' := by
          intro a b
          simp only [map_mul, toAdd_mul, zpow_add]
          exact ((hc x b).symm.zpow_right _).mul_mul_mul_comm _ _ }
    obtain ⟨y, hy⟩ := (hS f (by intro s hs; simp [f, hχ s hs])).surjective x
    have e := congrArg (fun t => (χ t).toAdd) hy
    change (χ (y * (x ^ 2) ^ (χ y).toAdd)).toAdd = (χ x).toAdd at e
    simp only [map_mul, map_zpow, map_pow, toAdd_mul, toAdd_zpow,
      toAdd_pow, zsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at e
    -- A preimage of x would force a positive integer to have a larger positive divisor.
    have hd : 1 + 2 * (χ x).toAdd ∣ (χ x).toAdd :=
      ⟨(χ y).toAdd, by simpa [add_mul, mul_add, mul_comm] using e.symm⟩
    have := Int.le_of_dvd hx hd
    omega
  have hi := nonpos g⁻¹
  simp only [map_inv, toAdd_inv] at hi
  exact le_antisymm (nonpos g) (by omega)

-- Evaluating integer characters on a finite test set embeds a free module of rank r.
private theorem rank_le_encard {r : ℕ} {S : Set (Free r)} (hS : IsTestSet S) :
    (r : ℕ∞) ≤ S.encard := by
  classical
  by_cases hfin : S.Finite
  · let := hfin.fintype
    let e := exponents r
    let eval : (Fin r → ℤ) →ₗ[ℤ] (S → ℤ) :=
      LinearMap.pi fun s => dotProductEquiv ℤ (Fin r) (e s).toAdd
    have hinj : Function.Injective eval := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      let χ := (dotProductEquiv ℤ (Fin r) v).toAddMonoidHom.toMultiplicative.comp e
      have hχ (s : Free r) (hs : s ∈ S) : (χ s).toAdd = 0 := by
        change dotProduct v (e s).toAdd = 0
        rw [dotProduct_comm]
        exact congrFun hv ⟨s, hs⟩
      obtain ⟨hc, he⟩ := satisfies_iff.mp (quotient_satisfies laws r)
      have hsq (x y : Free r) : Commute (x ^ 2) y :=
        commutatorElement_eq_one_iff_commute.mp
          (((hc x y x).symm.commutatorElement_pow_left 2).symm.trans (he x y))
      funext i
      have hz := character_zero hsq hS χ hχ (gen i)
      change dotProduct v (exponents r (gen i)).toAdd = 0 at hz
      simpa [exponents_gen, dotProduct_single_one] using hz
    rw [Set.encard, ENat.card_eq_coe_fintype_card, Nat.cast_le]
    simpa using card_le_of_injective ℤ eval hinj
  · rw [Set.Infinite.encard_eq hfin]
    exact le_top

private theorem free_hasTestRank (r : ℕ) : HasTestRank (Free r) r := by
  refine ⟨⟨_, gen_isTestSet r, le_antisymm ?_ (rank_le_encard (gen_isTestSet r))⟩,
    fun _ => rank_le_encard⟩
  rw [← Set.image_univ]
  simpa using Set.encard_image_le (@gen r) Set.univ

private theorem dihedral_satisfies : SatisfiesLaws laws (DihedralGroup 4) := by
  apply satisfies_iff.mpr
  simp only [Commute, SemiconjBy]
  decide

/-- **Negative answer to Timoshenko's test rank question, part (a).** There is a set $W$ of laws
in the free group $F_\mathbb{N}$ on countably many generators such that for every $r \ge 1$ the
free $r$-generator group $G_r$ of the variety defined by $W$ has test rank $r$, but the variety is
not abelian: some group satisfying the laws $W$ is not abelian.

The witness is the variety defined by $[[x, y], z] = 1$ and $[x, y]^p = 1$ for a prime $p$, which
contains the non-abelian group $\mathrm{UT}_3(\mathbb{F}_p)$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.87 (E. I. Timoshenko); resolution: M.
Kinyon and J. Urban (with Codex gpt-6-astra), Results on problems from the Kourovka Notebook,
preprint, version 4 (19 September 2026), Section 3.23 (Problem 16.87): the variety M_p defined by
[[x, y], z] = 1 and [x, y]^p = 1 (p prime) is nonabelian (it contains UT_3(F_p)) and nonperiodic
(it contains Z), and Proposition 3.9 shows that its free group of rank r has test rank r for
every r ≥ 1; the Kourovka Notebook (21st issue) marks 16.87 solved (a), b) No, it is not true in
both cases; AI solution confirmed by E. I. Timoshenko),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
theorem testRankVarietyAbelian_refuted : ¬ testRankVarietyAbelian := by
  intro h
  have hc := h laws (fun r _ => free_hasTestRank r) (DihedralGroup 4) dihedral_satisfies
  have hne : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by decide
  exact hne (hc _ _)

end MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87Wanted
