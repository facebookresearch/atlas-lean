/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.OrderOfElement

/-!
# Outer automorphisms of the category of free groups of a variety (Kourovka Notebook Problem 20.72)

Kourovka Notebook, Problem 20.72 (E. Plotkin), marked solved in the 21st issue: is there a variety
of groups `Θ` such that the group of automorphisms of the category of free finitely generated groups
`Θ⁰` contains outer automorphisms?

We prove the existence using the laws of the direct product of the infinite cyclic group and the
symmetric group on four letters.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.72 (E. Plotkin). UnsolvedMath record
UM-00701730 (`KOU-20.72`), dataset ulamai/UnsolvedMath v1.8.0.

A variety is given by a set `W` of laws in `x₀, x₁, …` (Birkhoff). Following Plotkin's setting as in
the resolving paper, `Θ⁰` has as objects the free groups `F_Θ(X)` of the variety for the finite
subsets `X` of a countable set `X⁰ = ℕ` and as morphisms all homomorphisms; `F_Θ(X)` is `FreeGroup
X` modulo its verbal subgroup. An automorphism of `Θ⁰` is a functor with a two-sided inverse
functor; it is inner when it is isomorphic to the identity functor (Definition 1.3 of the resolving
paper), and outer automorphisms exist exactly when some automorphism is not inner.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.VarietyCategoryOuterAutomorphismKourovka20Problem72Wanted

open CategoryTheory

/-- **Free group of a variety on a finite set.** Let $W$ be a set of words in the free group
$F(\mathbb{N})$ on $x_0, x_1, \ldots$, defining a variety $\Theta$, and let $X \subseteq \mathbb{N}$
be finite. The free group $F_\Theta(X)$ of $\Theta$ on $X$ is the quotient of the free group $F(X)$
on $X$ by its verbal subgroup, the normal closure of the set of values $\varphi(w)$ with $w \in W$
and $\varphi \colon F(\mathbb{N}) \to F(X)$ a homomorphism. This set of values is closed under
conjugation, so the verbal subgroup is also the subgroup it generates. -/
abbrev relativelyFreeGroup (W : Set (FreeGroup ℕ)) (X : Finset ℕ) : Type :=
  FreeGroup X ⧸ Subgroup.normalClosure {g | ∃ w ∈ W, ∃ φ : FreeGroup ℕ →* FreeGroup X, φ w = g}

/-- **Plotkin's category of free groups of a variety.** Let $W$ be a set of words in the free group
on $x_0, x_1, \ldots$, defining a variety $\Theta$. The category $\Theta^0$ has one object for each
finite subset $X$ of $X^0 = \mathbb{N}$, namely the free group $F_\Theta(X)$ of $\Theta$ on $X$, and
its morphisms are all group homomorphisms between these groups. -/
abbrev ThetaZero (W : Set (FreeGroup ℕ)) : Type :=
  InducedCategory GrpCat fun X : Finset ℕ => GrpCat.of (relativelyFreeGroup W X)

/-- **Plotkin's question on outer automorphisms of the category of free groups of a variety.** The
statement that there is a set $W$ of words in the free group on $x_0, x_1, \ldots$ such that, for
the variety $\Theta$ with laws $W$, the category $\Theta^0$ of the free groups of $\Theta$ on the
finite subsets of $\mathbb{N}$ has an automorphism that is not inner: functors
$\Phi, \Psi \colon \Theta^0 \to \Theta^0$ whose composites $\Psi \circ \Phi$ and $\Phi \circ \Psi$
both equal the identity functor, with $\Phi$ not naturally isomorphic to the identity functor.
This is Kourovka Notebook Problem 20.72 (E. Plotkin). -/
def existsVarietyWithNonInnerCategoryAutomorphism : Prop :=
  ∃ (W : Set (FreeGroup ℕ)) (Φ Ψ : ThetaZero W ⥤ ThetaZero W),
    Φ ⋙ Ψ = 𝟭 _ ∧ Ψ ⋙ Φ = 𝟭 _ ∧ IsEmpty (Φ ≅ 𝟭 _)

private abbrev PermFour := Equiv.Perm (Fin 4)
private abbrev Model := Multiplicative ℤ × PermFour

private def laws : Set (FreeGroup ℕ) := {w | ∀ ρ : FreeGroup ℕ →* Model, ρ w = 1}

private abbrev Rel (X : Finset ℕ) := relativelyFreeGroup laws X

private abbrev project {X : Finset ℕ} : FreeGroup X →* Rel X := QuotientGroup.mk' _

private abbrev gen {X : Finset ℕ} (i : X) : Rel X := project (FreeGroup.of i)

private def evaluate {X : Finset ℕ} (v : X → Model) : Rel X →* Model :=
  QuotientGroup.lift _ (FreeGroup.lift v) <| Subgroup.normalClosure_le_normal <| by
    rintro _ ⟨w, hw, f, rfl⟩
    exact hw ((FreeGroup.lift v).comp f)

private lemma evaluate_gen {X : Finset ℕ} (v : X → Model) (i : X) : evaluate v (gen i) = v i :=
  FreeGroup.lift_apply_of

-- Every law on X extends to a law on ℕ by renaming its letters. Substituting the original
-- letters back shows that evaluations in the model distinguish relatively free group elements.
private lemma eval_ext {X : Finset ℕ} {a b : Rel X}
    (h : ∀ v : X → Model, evaluate v a = evaluate v b) : a = b := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ b
  let incl := FreeGroup.map ((↑) : X → ℕ)
  let retract := FreeGroup.lift (fun n : ℕ => if hn : n ∈ X then FreeGroup.of (⟨n, hn⟩ : X) else 1)
  have leftInv : retract.comp incl = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp [incl, retract, i.property]
  apply div_eq_one.mp
  rw [← map_div]
  apply (QuotientGroup.eq_one_iff _).2
  apply Subgroup.subset_normalClosure
  refine ⟨incl (u / w), ?_, retract, DFunLike.congr_fun leftInv _⟩
  intro ρ
  let v := fun i : X => ρ (incl (FreeGroup.of i))
  have hv : ρ.comp incl = FreeGroup.lift v := FreeGroup.ext_hom _ _ (by simp [v])
  change (ρ.comp incl) (u / w) = 1
  rw [hv, map_div, div_eq_one]
  exact h v

private lemma perm_pow (p : PermFour) : p ^ 24 = 1 := by
  simpa [PermFour, Fintype.card_perm, show Nat.factorial 4 = 24 by decide] using
    (pow_card_eq_one (x := p))

private def flipPower (a : Model) : Model := (a.1, a.2 ^ 5)

private lemma flipPower_flipPower (a : Model) : flipPower (flipPower a) = a := by
  ext1
  · rfl
  · change (a.2 ^ 5) ^ 5 = a.2
    rw [← pow_mul, show 5 * 5 = 24 + 1 by decide, pow_succ, perm_pow, one_mul]

-- The 24th powers correct the exponent sum on the infinite cyclic factor and disappear
-- on the symmetric group. Thus the transported multiplication is itself a group word.
private def productWord {H : Type*} [Group H] (a b : H) : H :=
  (a ^ 5 * b ^ 5) ^ 5 / (a ^ 24 * b ^ 24)

private lemma map_productWord {H K : Type*} [Group H] [Group K] (f : H →* K) (a b : H) :
    f (productWord a b) = productWord (f a) (f b) := by simp [productWord]

private lemma productWord_model (a b : Model) :
    productWord a b = flipPower (flipPower a * flipPower b) := by
  apply Prod.ext
  · change (a.1 ^ 5 * b.1 ^ 5) ^ 5 / (a.1 ^ 24 * b.1 ^ 24) = a.1 * b.1
    simp only [mul_pow, ← pow_mul, show 5 * 5 = 24 + 1 by decide, pow_succ _ 24]
    rw [div_eq_iff_eq_mul]
    ac_rfl
  · change (a.2 ^ 5 * b.2 ^ 5) ^ 5 / (a.2 ^ 24 * b.2 ^ 24) = _
    simp [perm_pow, flipPower]

-- Conjugating a term function by flipPower in its inputs and output gives another term
-- function. The induction replaces every multiplication in the term by productWord.
private lemma exists_twist {X : Finset ℕ} (a : Rel X) :
    ∃ b : Rel X, ∀ v : X → Model, evaluate v b = flipPower (evaluate (flipPower ∘ v) a) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ a
  induction w with
  | one => exact ⟨1, fun v => by simp [flipPower]; rfl⟩
  | of i =>
    exact ⟨gen i, fun v => by
      change evaluate v (gen i) = flipPower (evaluate _ (gen i))
      rw [evaluate_gen, evaluate_gen]
      exact (flipPower_flipPower _).symm⟩
  | inv_of i ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨b⁻¹, fun v => by simp [hb, flipPower, inv_pow]⟩
  | mul x y hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨productWord b c, fun v => by
      simp only [map_productWord, hb, hc, productWord_model, flipPower_flipPower, map_mul]⟩

private noncomputable def twist {X : Finset ℕ} (a : Rel X) : Rel X := (exists_twist a).choose

private lemma eval_twist {X : Finset ℕ} (v : X → Model) (a : Rel X) :
    evaluate v (twist a) = flipPower (evaluate (flipPower ∘ v) a) := (exists_twist a).choose_spec v

private lemma twist_twist {X : Finset ℕ} (a : Rel X) : twist (twist a) = a := by
  apply eval_ext
  intro v
  simp only [eval_twist, flipPower_flipPower]
  rw [show flipPower ∘ (flipPower ∘ v) = v from funext fun _ => flipPower_flipPower _]

private lemma twist_gen {X : Finset ℕ} (i : X) : twist (gen i) = gen i := by
  apply eval_ext
  intro v
  rw [eval_twist, evaluate_gen, evaluate_gen]
  exact flipPower_flipPower _

private lemma twist_mul {X : Finset ℕ} (a b : Rel X) :
    twist (a * b) = productWord (twist a) (twist b) := by
  apply eval_ext
  intro v
  simp only [eval_twist, map_mul, map_productWord, productWord_model, flipPower_flipPower]

private lemma twist_productWord {X : Finset ℕ} (a b : Rel X) :
    twist (productWord a b) = twist a * twist b := by
  rw [← twist_twist a, ← twist_twist b, ← twist_mul, twist_twist, twist_twist, twist_twist]

private abbrev underlying {X Y : ThetaZero laws} (f : X ⟶ Y) : Rel X →* Rel Y := f.hom.hom

private lemma arrow_ext {X Y : ThetaZero laws} {f g : X ⟶ Y}
    (h : ∀ x, underlying f x = underlying g x) : f = g :=
  InducedCategory.hom_ext (GrpCat.hom_ext (MonoidHom.ext h))

private noncomputable def twistedFunctor : ThetaZero laws ⥤ ThetaZero laws where
  obj X := X
  map f := InducedCategory.homMk <| GrpCat.ofHom <| MonoidHom.mk'
    (fun x => twist (underlying f (twist x))) (fun x y => by
      rw [twist_mul, map_productWord, twist_productWord])
  map_id X := arrow_ext fun x => twist_twist x
  map_comp f g := by
    apply arrow_ext
    intro x
    change twist (underlying g (underlying f (twist x))) =
      twist (underlying g (twist (twist (underlying f (twist x)))))
    rw [twist_twist]

private lemma twistedFunctor_sq : twistedFunctor ⋙ twistedFunctor = 𝟭 _ := by
  refine Functor.hext ?_ ?_
  · exact fun _ => rfl
  intro X Y f
  apply heq_of_eq
  apply arrow_ext
  intro x
  change twist (twist (underlying f (twist (twist x)))) = underlying f x
  exact (twist_twist _).trans (congrArg (underlying f) (twist_twist (X := X) x))

private abbrev singletonSet : Finset ℕ := {0}

private abbrev generator : Rel singletonSet := gen (X := singletonSet) default

private def degree : Rel singletonSet →* Multiplicative ℤ :=
  (MonoidHom.fst _ _).comp (evaluate fun _ => (Multiplicative.ofAdd 1, 1))

private lemma degree_generator : degree generator = Multiplicative.ofAdd 1 := by
  exact congrArg Prod.fst
    (evaluate_gen (X := singletonSet) (fun _ => (Multiplicative.ofAdd 1, 1)) default)

private lemma exists_power (a : Rel singletonSet) : ∃ k : ℤ, a = generator ^ k := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ a
  refine ⟨FreeGroup.equivIntOfUnique w, ?_⟩
  exact (congrArg project (FreeGroup.equivIntOfUnique.left_inv w)).symm.trans (map_zpow _ _ _)

private abbrev rankOne : ThetaZero laws := singletonSet

private abbrev atElement {X : ThetaZero laws} (x : Rel X) : rankOne ⟶ X :=
  InducedCategory.homMk (GrpCat.ofHom ((zpowersHom _ x).comp degree))

private lemma atElement_generator {X : ThetaZero laws} (x : Rel X) :
    underlying (atElement x) generator = x := by
  change (zpowersHom _ x) (degree generator) = x
  rw [degree_generator, zpowersHom_apply]
  exact zpow_one _

-- The rank-one object is infinite cyclic. Its component in a natural isomorphism must
-- send the generator to itself or its inverse. Maps out of it then determine every component.
private lemma component_power (e : twistedFunctor ≅ 𝟭 _) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ ∀ (X : ThetaZero laws) (x : Rel X),
      underlying (e.hom.app X) (twist x) = x ^ k := by
  let f : Rel singletonSet →* Rel singletonSet := underlying (e.hom.app rankOne)
  let g : Rel singletonSet →* Rel singletonSet := underlying (e.inv.app rankOne)
  obtain ⟨k, hk⟩ := exists_power (f generator)
  obtain ⟨l, hl⟩ := exists_power (g generator)
  have hinv := congrArg (fun h : rankOne ⟶ rankOne => underlying h generator)
    (e.app rankOne).hom_inv_id
  change g (f generator) = generator at hinv
  rw [hk, map_zpow, hl, ← zpow_mul] at hinv
  have hkl := congrArg (fun g => (degree g).toAdd) hinv
  simp only [map_zpow, degree_generator, toAdd_zpow, toAdd_ofAdd,
    zsmul_eq_mul, mul_one] at hkl
  refine ⟨k, ?_, ?_⟩
  · exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one_right _ hkl)
  · intro X x
    have h := congrArg (fun h : rankOne ⟶ X => underlying h generator)
      (e.hom.naturality (atElement x))
    change underlying (e.hom.app X) (twist (underlying (atElement x) (twist generator))) =
      underlying (atElement x) (f generator) at h
    rw [show twist generator = generator from twist_gen _, atElement_generator, hk, map_zpow,
      atElement_generator] at h
    exact h

-- Specialize naturality to the product of two free generators, then evaluate them at
-- arbitrary permutations. This lets us disprove each of the two possible power identities.
private lemma perm_identity (e : twistedFunctor ≅ 𝟭 _) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ ∀ p q : PermFour,
      productWord (p ^ k) (q ^ k) = (p * q) ^ k := by
  obtain ⟨k, hk, h⟩ := component_power e
  refine ⟨k, hk, fun p q => ?_⟩
  let X : Finset ℕ := {0, 1}
  let i : X := ⟨0, by simp [X]⟩
  let j : X := ⟨1, by simp [X]⟩
  let f : Rel X →* Rel X := underlying (e.hom.app X)
  have hf (x : Rel X) : f (twist x) = x ^ k := h X x
  have hxy := hf (gen i * gen j)
  rw [twist_mul, map_productWord, hf, hf] at hxy
  let v (t : X) : Model := (1, if t.val = 0 then p else q)
  let ev : Rel X →* PermFour := (MonoidHom.snd _ _).comp (evaluate v)
  have heval (t : X) : ev (gen t) = (v t).2 := congrArg Prod.snd (evaluate_gen v t)
  have H := congrArg ev hxy
  simpa only [map_productWord, map_zpow, map_mul, heval, v, i, j, ite_true, ite_false,
    Nat.one_ne_zero] using H

private lemma twistedFunctor_outer : IsEmpty (twistedFunctor ≅ 𝟭 _) := by
  constructor
  intro e
  obtain ⟨k, hk, h⟩ := perm_identity e
  let p : PermFour := Equiv.swap 0 1
  rcases hk with rfl | rfl
  · -- The product of these transpositions has order three.
    let q : PermFour := Equiv.swap 1 2
    have H := h p q
    simp only [zpow_one, productWord, perm_pow, one_mul, div_one] at H
    rw [show p ^ 5 = p by decide, show q ^ 5 = q by decide] at H
    exact absurd (congrArg (fun r : PermFour => r 0) H) (by decide)
  · -- This time the two involutions have a product of order four.
    let q : PermFour := Equiv.swap 0 2 * Equiv.swap 1 3
    have H := h p q
    simp only [zpow_neg_one, productWord, perm_pow, one_mul, div_one] at H
    rw [show p⁻¹ ^ 5 = p by decide, show q⁻¹ ^ 5 = q by decide] at H
    exact absurd (congrArg (fun r : PermFour => r 0) H) (by decide)

/--
**Some variety of groups has an outer automorphism of its category of free groups.** There is a
set $W$ of words in the free group on $x_0, x_1, \ldots$ such that, for the variety $\Theta$ with
laws $W$, the category $\Theta^0$, whose objects are the free groups $F_\Theta(X)$ of $\Theta$ on
the finite subsets $X \subseteq \mathbb{N}$ and whose morphisms are all group homomorphisms, has an
automorphism that is not inner: there are functors $\Phi, \Psi \colon \Theta^0 \to \Theta^0$ whose
composites $\Psi \circ \Phi$ and $\Phi \circ \Psi$ both equal the identity functor, and $\Phi$ is
not naturally isomorphic to the identity functor.

Barbosa Fernandes and Tsurkov (Theorem 9.1) show that for the variety of metabelian groups of
exponent $4$ and nilpotency class at most $4$ (laws $x^4 = 1$, $((x_1, x_2), (x_3, x_4)) = 1$ and
$((((x_1, x_2), x_3), x_4), x_5) = 1$) the group of automorphisms of $\Theta^0$ modulo the inner
ones has order $2$. The 21st issue of the Kourovka Notebook marks 20.72 solved ("Yes, there is").

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 20.72 (E. Plotkin); resolution: R. Barbosa Fernandes and
A. Tsurkov, Automorphisms of the category of finitely generated free groups of the some subvariety
of the variety of all groups, preprint, arXiv:1909.05955 (2019), Theorem 9.1: for the variety Θ
defined by x⁴ = 1, ((x₁, x₂), (x₃, x₄)) = 1 and ((((x₁, x₂), x₃), x₄), x₅) = 1, the quotient A/Y of
the automorphism group of Θ⁰ by the inner automorphisms has order 2; Kourovka Notebook (21st issue),
Problem 20.72: Yes, there is, https://arxiv.org/abs/1909.05955.
-/
theorem existsVarietyWithNonInnerCategoryAutomorphism_holds :
    existsVarietyWithNonInnerCategoryAutomorphism :=
  ⟨laws, twistedFunctor, twistedFunctor, twistedFunctor_sq, twistedFunctor_sq, twistedFunctor_outer⟩

end MathlibExt.GroupTheory.VarietyCategoryOuterAutomorphismKourovka20Problem72Wanted
