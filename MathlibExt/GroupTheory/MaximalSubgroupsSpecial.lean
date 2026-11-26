/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Frattini
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Ring

/-!
# Finite `p`-groups whose maximal subgroups are special (Kourovka Notebook Problem 16.13)

The upper unitriangular groups of degree three over finite extension fields supply arbitrarily large
examples for every prime.

Kourovka Notebook, Archive of Solved Problems, Problem 16.13 (Ya. G. Berkovich): does there exist a
finite `p`-group `G` all of whose maximal subgroups `H` are special, that is, satisfy `Z(H) = [H, H]
= Φ(H)`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.13 (Ya. G.
Berkovich). UnsolvedMath record UM-00701205 (`KOU-16.13`), dataset ulamai/UnsolvedMath v1.8.0.

The literal existence question is trivially true: in the group of order `p` the only maximal
subgroup is trivial and satisfies `Z = [H, H] = Φ = 1`. The target is the Archive's answer, "for all
primes there are groups of arbitrarily large size with this property": for every prime `p` and every
`n` there is such a `G` with `|G| > n`. When `|G| > p²` every maximal subgroup has order at least
`p²`, and the condition forces it to be non-abelian. Maximal subgroups are the coatoms of the
subgroup lattice.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalSubgroupsSpecialKourovka16Problem13Wanted

/-- **Special group.** A group $H$ is special when its center, its commutator subgroup and its
Frattini subgroup coincide: $Z(H) = [H, H] = \Phi(H)$. -/
def IsSpecialGroup (H : Type*) [Group H] : Prop :=
  Subgroup.center H = commutator H ∧ commutator H = frattini H

/-- **Kourovka Problem 16.13, strong form (statement).** The statement that for every prime $p$
and every natural number $n$ there is a finite $p$-group $G$ of order greater than $n$ all of whose
maximal subgroups $H$ are special, that is, have center $Z(H)$, commutator subgroup $[H, H]$ and
Frattini subgroup $\Phi(H)$ all equal. This is the form in which the problem was resolved; the
problem as posed asks only for one finite $p$-group all of whose maximal subgroups are special. -/
def largePGroupsWithSpecialMaximalSubgroups : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G),
    IsPGroup p G ∧ n < Nat.card G ∧ ∀ H : Subgroup G, IsCoatom H → IsSpecialGroup H

/-- Coordinates above the diagonal of a unitriangular matrix of degree three. -/
@[ext] private structure Heisenberg (K : Type*) where
  x : K
  y : K
  z : K

namespace Heisenberg

open scoped commutatorElement

variable {K : Type*} [Field K]

private def mul (a b : Heisenberg K) : Heisenberg K :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩

private def inv (a : Heisenberg K) : Heisenberg K :=
  ⟨-a.x, -a.y, -a.z + a.x * a.y⟩

private instance heisenbergGroup : Group (Heisenberg K) where
  one := ⟨0, 0, 0⟩
  mul := mul
  inv := inv
  mul_assoc a b c := by
    change (a.mul b).mul c = a.mul (b.mul c)
    apply Heisenberg.ext <;> dsimp [mul] <;> ring
  one_mul a := by
    change (Heisenberg.mk 0 0 0).mul a = a
    apply Heisenberg.ext <;> simp [mul]
  mul_one a := by
    change a.mul ⟨0, 0, 0⟩ = a
    apply Heisenberg.ext <;> simp [mul]
  inv_mul_cancel a := by
    change a.inv.mul a = ⟨0, 0, 0⟩
    apply Heisenberg.ext <;> dsimp [mul, inv] <;> ring

private def equivProd : Heisenberg K ≃ K × K × K where
  toFun a := (a.x, a.y, a.z)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

private instance heisenbergFinite [Finite K] : Finite (Heisenberg K) :=
  Finite.of_equiv _ equivProd.symm

omit [Field K] in
private theorem card : Nat.card (Heisenberg K) = Nat.card K ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod]
  ring

private theorem commutator_coords (a b : Heisenberg K) :
    ⁅a, b⁆ = ⟨0, 0, a.x * b.y - b.x * a.y⟩ := by
  change ((a.mul b).mul a.inv).mul b.inv = _
  apply Heisenberg.ext <;> dsimp [mul, inv] <;> ring

private def xAxis : Multiplicative K →* Heisenberg K where
  toFun a := ⟨a.toAdd, 0, 0⟩
  map_one' := rfl
  map_mul' a b := by
    change Heisenberg.mk (a.toAdd + b.toAdd) 0 0 = (Heisenberg.mk a.toAdd 0 0).mul ⟨b.toAdd, 0, 0⟩
    simp [mul]

private def yAxis : Multiplicative K →* Heisenberg K where
  toFun b := ⟨0, b.toAdd, 0⟩
  map_one' := rfl
  map_mul' a b := by
    change Heisenberg.mk 0 (a.toAdd + b.toAdd) 0 = (Heisenberg.mk 0 a.toAdd 0).mul ⟨0, b.toAdd, 0⟩
    simp [mul]

private def horizontal : Heisenberg K →* Multiplicative (K × K) where
  toFun a := Multiplicative.ofAdd (a.x, a.y)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A quotient smaller than a coordinate axis kills a nonzero element of that axis. -/
private theorem axis_kernel {Q : Type*} [Group Q] [Finite Q]
    (f : Multiplicative K →* Q) (h : Nat.card Q < Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ f (.ofAdd a) = 1 := by
  by_contra! hn
  have hinj := (injective_iff_map_eq_one f).2 fun a ha => by
    by_contra hne
    exact hn a.toAdd hne ha
  exact h.not_ge (Nat.card_le_card_of_injective _ hinj)

/-- A homomorphism into a group of prime order is trivial or surjective. -/
private theorem trivial_or_surjective {A Q : Type*} [Group A] [Group Q]
    [Fact (Nat.card Q).Prime] (f : A →* Q) :
    (∀ a, f a = 1) ∨ Function.Surjective f := by
  rcases f.range.eq_bot_or_eq_top_of_prime_card with h | h
  · exact Or.inl fun a => DFunLike.congr_fun (MonoidHom.range_eq_bot_iff.mp h) a
  · exact Or.inr (MonoidHom.range_eq_top.mp h)

/-- In a finite p-group, maximal subgroups have cyclic quotient and contain all commutators. -/
private theorem derived_le_frattini {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) : commutator A ≤ frattini A := by
  have := hA.isNilpotent
  apply le_iInf₂
  intro M hM
  change IsCoatom M at hM
  have : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
  have hcard := M.index_eq_card.symm.trans (hA.isCoatom_iff_index_eq_prime.mp hM)
  have := isCyclic_of_prime_card hcard
  let := IsCyclic.commGroup (α := A ⧸ M)
  simpa only [QuotientGroup.ker_mk'] using
    Group.Abelianization.commutator_le_ker (QuotientGroup.mk' M)

/-- Linear functionals separate horizontal coordinates from the Frattini subgroup. -/
private theorem frattini_le_horizontal_ker {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) K]
    (H : Subgroup (Heisenberg K)) : frattini H ≤ (horizontal.domRestrict H).ker := by
  intro a ha
  change (a.1.x, a.1.y) = 0
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod p) _).mp
  intro φ
  let f := φ.toAddMonoidHom.toMultiplicative.comp (horizontal.domRestrict H)
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
  have : Fact (Nat.card (Multiplicative (ZMod p))).Prime := ⟨by rw [hcard]; exact hp.out⟩
  change f a = 1
  rcases trivial_or_surjective f with h | h
  · exact h a
  · apply frattini_le_coatom (K := f.ker) _ ha
    apply Subgroup.isCoatom_of_index_prime
    simpa only [Subgroup.index_ker, MonoidHom.range_eq_top.mpr h, Subgroup.card_top, hcard]
      using hp.out

private theorem special_coatom {p : ℕ} [hp : Fact p.Prime] [Finite K] [Algebra (ZMod p) K]
    (hG : IsPGroup p (Heisenberg K)) (hsize : p < Nat.card K)
    (H : Subgroup (Heisenberg K)) (hH : IsCoatom H) : IsSpecialGroup H := by
  have := hG.isNilpotent
  have : H.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom H Group.normalizerCondition_of_isNilpotent hH
  let q := QuotientGroup.mk' H
  have hq := H.index_eq_card.symm.trans (hG.isCoatom_iff_index_eq_prime.mp hH)
  have : Fact (Nat.card (Heisenberg K ⧸ H)).Prime := ⟨by rw [hq]; exact hp.out⟩
  obtain ⟨a, ha, hax⟩ := axis_kernel (q.comp xAxis) (hq.trans_lt hsize)
  obtain ⟨b, hb, hby⟩ := axis_kernel (q.comp yAxis) (hq.trans_lt hsize)
  let X : H := ⟨xAxis (.ofAdd a), (QuotientGroup.eq_one_iff _).mp hax⟩
  let Y : H := ⟨yAxis (.ofAdd b), (QuotientGroup.eq_one_iff _).mp hby⟩
  let Z := (horizontal.domRestrict H).ker
  have hcenter : Subgroup.center H = Z := by
    ext g
    change _ ↔ (g.1.x, g.1.y) = 0
    rw [Subgroup.mem_center_iff]
    constructor
    · intro h
      have hx := congrArg (fun t : H => t.1.z) (h Y)
      have hy := congrArg (fun t : H => t.1.z) (h X)
      change 0 + g.1.z + 0 * g.1.y = g.1.z + 0 + g.1.x * b at hx
      change 0 + g.1.z + a * g.1.y = g.1.z + 0 + g.1.x * 0 at hy
      simpa [hb, ha] using And.intro hx hy
    · intro h t
      have hx : g.1.x = 0 := congrArg Prod.fst h
      have hy : g.1.y = 0 := congrArg Prod.snd h
      apply Subtype.ext
      change t.1.mul g.1 = g.1.mul t.1
      apply Heisenberg.ext <;> simp [mul, hx, hy, add_comm]
  have hderived : Z ≤ commutator H := by
    intro g hg
    change (g.1.x, g.1.y) = 0 at hg
    have hx : g.1.x = 0 := congrArg Prod.fst hg
    have hy : g.1.y = 0 := congrArg Prod.snd hg
    suffices ∃ u v : H, u.1.x * v.1.y - v.1.x * u.1.y = g.1.z by
      obtain ⟨u, v, huv⟩ := this
      have heq : ⁅u, v⁆ = g := by
        apply Subtype.ext
        change ⁅u.1, v.1⁆ = g.1
        rw [commutator_coords]
        exact Heisenberg.ext hx.symm hy.symm huv
      exact heq ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
    -- If the entire x-axis lies in H, vary it against Y. Otherwise it covers the quotient,
    -- so every y-coordinate has a representative in H, which we pair with X.
    rcases trivial_or_surjective (q.comp xAxis) with hall | hon
    · let u : H := ⟨xAxis (.ofAdd (g.1.z / b)), (QuotientGroup.eq_one_iff _).mp (hall _)⟩
      exact ⟨u, Y, by change g.1.z / b * b - 0 * 0 = _; simp [hb]⟩
    · let v := yAxis (.ofAdd (g.1.z / a))
      obtain ⟨c, hc⟩ := hon (q v)⁻¹
      have hv : xAxis c * v ∈ H := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (xAxis c * v) = 1
        rw [map_mul, show q (xAxis c) = _ from hc, inv_mul_cancel]
      refine ⟨X, ⟨_, hv⟩, ?_⟩
      change a * (0 + g.1.z / a) - (c.toAdd + 0) * 0 = _
      simp [mul_div_cancel₀ _ ha]
  have hΦ := derived_le_frattini (hG.to_subgroup H)
  have hker := frattini_le_horizontal_ker (p := p) H
  exact ⟨hcenter.trans (le_antisymm hderived (hΦ.trans hker)),
    le_antisymm hΦ (hker.trans hderived)⟩

end Heisenberg

/--
**Arbitrarily large $p$-groups all of whose maximal subgroups are special.** For every prime $p$
and every natural number $n$ there is a finite $p$-group $G$ of order greater than $n$ such that
every maximal subgroup $H$ of $G$ is special, that is, its center $Z(H)$, its commutator subgroup
$[H, H]$ and its Frattini subgroup $\Phi(H)$ coincide. This answers Kourovka Problem 16.13
positively.

The Kourovka Archive records this answer, citing Cossey (2014); for $p = 2$ a Sylow $2$-subgroup of
$L_3(4)$ is another example (Zenkov).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.13 (Ya. G.
Berkovich); resolution: J. Cossey, Bull. Austral. Math. Soc. 89 (2014), 415-419, Kourovka Archive,
Problem 16.13 (for all primes, groups of arbitrarily large size; for p = 2 also a Sylow 2-subgroup
of L_3(4), V. I. Zenkov, 2014).
-/
theorem largePGroupsWithSpecialMaximalSubgroups_holds :
    largePGroupsWithSpecialMaximalSubgroups := by
  intro p hp n
  have : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p (n + 2)
  have hK : Nat.card K = p ^ (n + 2) := GaloisField.card _ _ (by omega)
  have hG : Nat.card (Heisenberg K) = p ^ ((n + 2) * 3) := by
    rw [Heisenberg.card, hK, pow_mul]
  have hP := IsPGroup.of_card hG
  refine ⟨Heisenberg K, inferInstance, inferInstance, hP, ?_, Heisenberg.special_coatom hP ?_⟩
  · rw [hG]
    exact lt_trans (by omega : n < (n + 2) * 3) (Nat.lt_pow_self hp.one_lt)
  · rw [hK]
    simpa using (pow_lt_pow_right₀ hp.one_lt (by omega : 1 < n + 2))

end MathlibExt.GroupTheory.MaximalSubgroupsSpecialKourovka16Problem13Wanted
