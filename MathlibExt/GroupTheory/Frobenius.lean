/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/Frobenius.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `frobenius_kernel_isNormal`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/frobenius_kernel_isNormal.toml`, rev 1, submitter Kim Morrison, status
archived): the statement of `frobenius_kernel_isNormal`, with the docstring and the module
documentation it had in the former wanted module `WantedExt/GroupTheory/FrobeniusWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.GroupTheory.FrobeniusWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): the `theorem_wanted` was proved and the declaration moved from
`WantedExt/GroupTheory/FrobeniusWanted.lean` to this `MathlibExt` module with unchanged name,
statement and docstring, and the import of `Batteries.Util.ProofWanted` was dropped.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`frobenius_kernel_isNormal`, the private lemmas it uses, the title, first paragraph and proof
outline of the module documentation, and the linter options.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic
import MathlibExt.GroupTheory.BurnsidePaqb.CharacterOrthogonality
import MathlibExt.GroupTheory.BurnsidePaqb.ScalarCenter

/-!
# Frobenius's theorem: the Frobenius kernel is normal

This file proves `MathlibExt.GroupTheory.FrobeniusWanted.GroupTheory.frobenius_kernel_isNormal`:
the identity together with the fixed-point-free elements of a Frobenius group is a normal
subgroup.

Frobenius's theorem on Frobenius groups.

A *Frobenius group* is a finite group `G` acting transitively and faithfully on
a set `X` (with `|X| ≥ 2`) such that:
* point stabilisers are non-trivial, and
* no non-identity element of `G` fixes more than one point of `X`.

Frobenius's theorem (1901) states that the *Frobenius kernel*
  `K = {1} ∪ {g ∈ G | g fixes no point of X}`
is a normal subgroup of `G`. The only known proof uses character theory
(induction of characters from a point stabiliser to `G`); no purely
group-theoretic proof has been found in over a century.

## Proof outline

The proof is the classical character-theoretic argument. Fix a point `x₀` with stabiliser `H`,
and pair complex functions on a finite group by `⟨f₁, f₂⟩ = |G|⁻¹ ∑ g, f₁ g * f₂ g⁻¹`. For a
function `θ` on `H`, the induced class function is `θᴳ g = |H|⁻¹ ∑ x, θ° (x g x⁻¹)`, where `θ°`
extends `θ` by zero, and Frobenius reciprocity `⟨θᴳ, ψ⟩ = ⟨θ, ψ|_H⟩` holds for every class
function `ψ` on `G`. Since a nonidentity element of `H` fixes no point other than `x₀`, if `θ`
is a class function vanishing at `1` then `θᴳ` restricts to `θ` on `H`, and `θᴳ` vanishes on
`K`.

For an irreducible character `φ` of `H`, the class function `φ* = (φ - φ(1))ᴳ + φ(1)` restricts to
`φ` on `H`, is constant equal to `φ(1)` on `K`, satisfies `⟨φ*, φ*⟩ = 1`, and has integral
inner products with the irreducible characters of `G` (differences of dimensions of spaces of
invariants and of intertwining maps). Expanding `φ*` in the irreducible characters of `G` shows
that `φ*` is itself an irreducible character. The intersection `N` of the kernels of the
corresponding representations is a normal subgroup. A character takes the value of its degree
only on the kernel of its representation, so `K ⊆ N`. Conversely, an element of `N` that fixes a
point is conjugate into `H`, where every irreducible character of `H` takes the value of its
degree, so it is the identity; hence `N = K`.

The orthonormality and completeness of irreducible characters, the regular character and the
eigenvalue argument come from the `MathlibExt.GroupTheory.BurnsidePaqb` modules.
-/

public section

namespace MathlibExt.GroupTheory.FrobeniusWanted
namespace GroupTheory

open BurnsidePaqb CategoryTheory

/-! ### The pairing of complex functions on a finite group -/

/-- The bilinear pairing `⟨f₁, f₂⟩ = |G|⁻¹ ∑ g, f₁ g * f₂ g⁻¹` of complex functions on a finite
group. -/
private noncomputable def pair (G : Type*) [Group G] [Fintype G] :
    (G → ℂ) →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f₁ f₂ => (Nat.card G : ℂ)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹)
    (fun f₁ f₁' f₂ => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
    (fun c f₁ f₂ => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun f₁ f₂ f₂' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c f₁ f₂ => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

private theorem pair_apply {G : Type*} [Group G] [Fintype G] (f₁ f₂ : G → ℂ) :
    pair G f₁ f₂ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹ := rfl

private theorem pair_comm {G : Type*} [Group G] [Fintype G] (f₁ f₂ : G → ℂ) :
    pair G f₁ f₂ = pair G f₂ f₁ := by
  rw [pair_apply, pair_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp [mul_comm]

private theorem pair_one_one {G : Type*} [Group G] [Fintype G] :
    pair G 1 1 = 1 := by
  rw [pair_apply]
  simp only [Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ### Induced class functions -/

open scoped Classical in
/-- The extension by zero of a function on a subgroup. -/
private noncomputable def extZero {G : Type*} [Group G] (H : Subgroup G) (f : H → ℂ) (g : G) :
    ℂ :=
  if hg : g ∈ H then f ⟨g, hg⟩ else 0

private theorem extZero_of_mem {G : Type*} [Group G] (H : Subgroup G) (f : H → ℂ) {g : G}
    (hg : g ∈ H) : extZero H f g = f ⟨g, hg⟩ := by
  simp [extZero, hg]

private theorem extZero_of_notMem {G : Type*} [Group G] (H : Subgroup G) (f : H → ℂ) {g : G}
    (hg : g ∉ H) : extZero H f g = 0 := by
  simp [extZero, hg]

/-- The class function induced from a function on a subgroup:
`ind f g = |H|⁻¹ ∑ x, f° (x g x⁻¹)`, where `f°` is the extension of `f` by zero. -/
private noncomputable def ind {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ)
    (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x : G, extZero H f (x * g * x⁻¹)

private theorem ind_conj {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ)
    (g h : G) : ind H f (h * g * h⁻¹) = ind H f g := by
  unfold ind
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun x => by
    simp only [Equiv.coe_mulRight]
    congr 1
    group

private theorem sum_extZero_mul {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H]
    (f : H → ℂ) (ψ : G → ℂ) :
    ∑ y : G, extZero H f y * ψ y = ∑ h : H, f h * ψ h := by
  classical
  have h1 : ∑ h : H, f h * ψ h =
      ∑ y ∈ Finset.univ.filter (· ∈ H), extZero H f y * ψ y := by
    rw [Finset.sum_subtype (p := (· ∈ H)) (Finset.univ.filter (· ∈ H)) (fun x => by simp)
      (fun y => extZero H f y * ψ y)]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [extZero_of_mem H f h.2]
  rw [h1, Finset.sum_filter_of_ne]
  intro y _ hy
  by_contra hyH
  exact hy (by rw [extZero_of_notMem H f hyH, zero_mul])

/-- **Frobenius reciprocity** for the pairing: `⟨ind f, ψ⟩_G = ⟨f, ψ|_H⟩_H` for a class
function `ψ` on `G`. -/
private theorem pair_ind {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H]
    (f : H → ℂ) (ψ : G → ℂ) (hψ : ∀ g h : G, ψ (h * g * h⁻¹) = ψ g) :
    pair G (ind H f) ψ = pair H f (fun h => ψ h) := by
  rw [pair_apply, pair_apply]
  have hinner : ∀ x : G, ∑ g : G, extZero H f (x * g * x⁻¹) * ψ g⁻¹ =
      ∑ y : G, extZero H f y * ψ y⁻¹ := by
    intro x
    exact Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ fun g => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      congr 1
      rw [show (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ by group]
      exact (hψ g⁻¹ x).symm
  have hS : ∑ g : G, ind H f g * ψ g⁻¹ =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, ∑ g : G, extZero H f (x * g * x⁻¹) * ψ g⁻¹ := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ind, mul_assoc, Finset.sum_mul]
  rw [hS]
  simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  rw [sum_extZero_mul H f (fun y => ψ y⁻¹)]
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp only [InvMemClass.coe_inv]
  field_simp

/-! ### Frobenius actions -/

section Frobenius

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X} {H : Subgroup G}

private theorem mem_of_conj_mem (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {h : G} (hh : h ∈ H) (h1 : h ≠ 1) {x : G} (hx : x * h * x⁻¹ ∈ H) : x ∈ H := by
  rw [hH] at hh hx ⊢
  have h2 : h • (x⁻¹ • x₀) = x⁻¹ • x₀ := by
    have := congrArg (x⁻¹ • ·) hx
    simpa only [mul_smul, inv_smul_smul] using this
  have h3 := hfrob h h1 _ _ h2 hh
  calc x • x₀ = x • (x⁻¹ • x₀) := by rw [h3]
    _ = x₀ := smul_inv_smul x x₀

private theorem conj_notMem_of_forall_ne (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀) {k : G}
    (hk : ∀ x : X, k • x ≠ x) (x : G) : x * k * x⁻¹ ∉ H := by
  intro hx
  rw [hH] at hx
  apply hk (x⁻¹ • x₀)
  have := congrArg (x⁻¹ • ·) hx
  simpa only [mul_smul, inv_smul_smul] using this

variable [Fintype G]

/-- In a Frobenius action, inducing a class function of a point stabiliser that vanishes at `1`
and restricting back gives the same function. -/
private theorem ind_apply_coe (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (θ : H → ℂ) (hθ : ∀ g h, θ (h * g * h⁻¹) = θ g) (hθ1 : θ 1 = 0) (h : H) :
    ind H θ h = θ h := by
  classical
  by_cases h1 : h = 1
  · subst h1
    have hterm : ∀ x : G, extZero H θ (x * ((1 : H) : G) * x⁻¹) = 0 := by
      intro x
      rw [OneMemClass.coe_one, mul_one, mul_inv_cancel, extZero_of_mem H θ H.one_mem]
      exact hθ1
    simp only [ind, hterm, Finset.sum_const_zero, mul_zero]
    exact hθ1.symm
  · have hG1 : (h : G) ≠ 1 := fun h' => h1 (Subtype.ext h')
    have hterm : ∀ x : G, extZero H θ (x * h * x⁻¹) = if x ∈ H then θ h else 0 := by
      intro x
      split_ifs with hx
      · rw [extZero_of_mem H θ (H.mul_mem (H.mul_mem hx h.2) (H.inv_mem hx))]
        have : (⟨x * h * x⁻¹, H.mul_mem (H.mul_mem hx h.2) (H.inv_mem hx)⟩ : H) =
            ⟨x, hx⟩ * h * ⟨x, hx⟩⁻¹ := rfl
        rw [this, hθ]
      · exact extZero_of_notMem H θ fun hmem => hx (mem_of_conj_mem hH hfrob h.2 hG1 hmem)
    simp only [ind, hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (· ∈ H)).card : ℂ) = Nat.card H := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]

/-- In a Frobenius action, a class induced from a function of a point stabiliser vanishing at
`1` vanishes at `1` and at every element without fixed points. -/
private theorem ind_apply_eq_zero (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀) (θ : H → ℂ)
    (hθ1 : θ 1 = 0) {k : G} (hk : k = 1 ∨ ∀ x : X, k • x ≠ x) : ind H θ k = 0 := by
  unfold ind
  rw [Finset.sum_eq_zero, mul_zero]
  intro x _
  rcases hk with rfl | hk
  · rw [mul_one, mul_inv_cancel, extZero_of_mem _ θ (Subgroup.one_mem _)]
    exact hθ1
  · exact extZero_of_notMem _ θ (conj_notMem_of_forall_ne hH hk x)

end Frobenius

/-! ### Characters -/

private theorem exists_eq_of_sum_sq_eq_one {ι : Type*} [Fintype ι] (n : ι → ℤ)
    (h : ∑ i, n i ^ 2 = 1) : ∃ i, n i ^ 2 = 1 ∧ ∀ j, j ≠ i → n j = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at h
  have hi1 : 0 < n i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => n j ^ 2) (Finset.mem_univ i)
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i, n j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hrest : ∑ j ∈ Finset.univ.erase i, n j ^ 2 = 0 := by
    have hi1' : 1 ≤ n i ^ 2 := hi1
    linarith
  have hi2 : n i ^ 2 = 1 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at hrest
  refine ⟨i, hi2, fun j hj => ?_⟩
  exact pow_eq_zero_iff two_ne_zero |>.mp
    (hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))

/-- A class function of norm `1` with integral inner products against the irreducible
characters and positive value at `1` is an irreducible character. -/
private theorem exists_charFun_eq {G : Type} [Group G] [Fintype G] (ψ : G → ℂ)
    (hψ : IsClassFun G ψ) (hnorm : pair G ψ ψ = 1)
    (hint : ∀ c : Irr G, ∃ n : ℤ, pair G ψ (Irr.charFun G c) = n)
    (d : ℕ) (hd : 0 < d) (hψ1 : ψ 1 = d) : ∃ c₀ : Irr G, ψ = Irr.charFun G c₀ := by
  classical
  choose n hn using hint
  have hexp : ψ = ∑ c : Irr G, (n c : ℂ) • Irr.charFun G c := by
    conv_lhs => rw [classfun_expand G hψ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hn c, pair_apply]
  have hsq : ∑ c : Irr G, n c ^ 2 = 1 := by
    have h1 : pair G ψ ψ = ∑ c : Irr G, (n c : ℂ) * (n c : ℂ) := by
      conv_lhs => arg 2; rw [hexp]
      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul, hn c, smul_eq_mul]
    rw [hnorm] at h1
    have h2 : ((∑ c : Irr G, n c ^ 2 : ℤ) : ℂ) = 1 := by
      push_cast
      simp only [pow_two]
      exact h1.symm
    exact_mod_cast h2
  obtain ⟨c₀, hc₀, hzero⟩ := exists_eq_of_sum_sq_eq_one n hsq
  have hψc : ψ = (n c₀ : ℂ) • Irr.charFun G c₀ := by
    rw [hexp, Finset.sum_eq_single c₀ (fun c _ hc => by rw [hzero c hc]; simp)
      (fun h => absurd (Finset.mem_univ c₀) h)]
  have hn1 : n c₀ = 1 := by
    have hval := congrFun hψc 1
    rw [hψ1, Pi.smul_apply, Irr.charFun_one, smul_eq_mul] at hval
    have hval' : (d : ℤ) = n c₀ * (Module.finrank ℂ (Irr.repBundle G c₀).1 : ℤ) := by
      exact_mod_cast hval
    have hsq' : n c₀ = 1 ∨ n c₀ = -1 := by
      have : (n c₀ - 1) * (n c₀ + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases hsq' with h | h
    · exact h
    · rw [h] at hval'
      have : (0 : ℤ) ≤ (Module.finrank ℂ (Irr.repBundle G c₀).1 : ℤ) := by positivity
      omega
  exact ⟨c₀, by rw [hψc, hn1, Int.cast_one, one_smul]⟩

/-- If the character of a simple representation takes its degree at `g`, then `g` acts
trivially. -/
private theorem rho_eq_one_of_character_eq {G : Type} [Group G] [Finite G] (V : FDRep ℂ G)
    [Simple V] (hpos : 0 < Module.finrank ℂ V) (g : G) (hg : V.character g = V.character 1) :
    V.ρ g = 1 := by
  have := irreducible_of_simple_fdrep G V
  have : Nontrivial V := Module.finrank_pos_iff.mp hpos
  have hchar : Representation.character (V.ρ : Representation ℂ G V) g = Module.finrank ℂ V := by
    rw [← FDRep.char_one V, ← hg]
    rfl
  have hnorm : ‖Representation.character (V.ρ : Representation ℂ G V) g‖ = Module.finrank ℂ V := by
    rw [hchar, Complex.norm_natCast]
  have hall := all_roots_eq_of_norm_eq (V.ρ : Representation ℂ G V) g hnorm
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, μ₀ ∈ (V.ρ g).charpoly.roots := by
    have hcard := charpoly_roots_card (V.ρ : Representation ℂ G V) g
    exact Multiset.card_pos_iff_exists_mem.mp (hcard ▸ hpos)
  have hsmul := eq_smul_one_of_all_roots_eq (V.ρ : Representation ℂ G V) g μ₀
    (fun μ hμ => hall μ hμ μ₀ hμ₀)
  have htr : Representation.character (V.ρ : Representation ℂ G V) g = μ₀ * Module.finrank ℂ V := by
    change LinearMap.trace ℂ V (V.ρ g) = _
    rw [hsmul, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hμ : μ₀ = 1 := by
    rw [hchar] at htr
    have hne : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact mul_right_cancel₀ hne (htr.symm.trans (one_mul _).symm)
  rw [hsmul, hμ, one_smul]

/-- An element of a finite group at which every irreducible character takes its degree is the
identity. -/
private theorem eq_one_of_forall_charFun_eq {H : Type} [Group H] [Finite H] (h : H)
    (hh : ∀ c : Irr H, Irr.charFun H c h = Irr.charFun H c 1) : h = 1 := by
  have := Fintype.ofFinite H
  by_contra hne
  have h1 := regular_character_vanishes H h hne
  have h2 := sum_deg_sq H
  simp only [hh, ← pow_two] at h1
  rw [h1] at h2
  exact Fintype.card_ne_zero (α := H) (by exact_mod_cast h2.symm)

/-- The pairing of two characters is the dimension of a space of intertwining maps. -/
private theorem pair_character_character {G : Type} [Group G] [Fintype G] {V W : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ G V) (ρ : Representation ℂ G W) :
    pair G σ.character ρ.character = Module.finrank ℂ (Representation.IntertwiningMap ρ σ) :=
  Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ

/-- The pairing of the trivial character with a character is the dimension of the invariants. -/
private theorem pair_one_character {G : Type} [Group G] [Fintype G] {W : Type}
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) :
    pair G 1 ρ.character = Module.finrank ℂ (Representation.invariants ρ) := by
  rw [pair_comm, pair_apply, ← Representation.card_inv_mul_sum_char_eq_finrank]
  simp only [Pi.one_apply, mul_one]

private theorem finrank_repBundle_pos {G : Type} [Group G] [Finite G] (c : Irr G) :
    0 < Module.finrank ℂ (Irr.repBundle G c).1 := by
  have := (Irr.repBundle G c).2
  have := irreducible_of_simple_fdrep G (Irr.repBundle G c).1
  have : Nontrivial (Irr.repBundle G c).1 := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G)
    (Representation.asModule ((Irr.repBundle G c).1.ρ : Representation ℂ G (Irr.repBundle G c).1))
  exact Module.finrank_pos

/-! ### The extended characters -/

/-- The class function `φ* = (φ - φ(1))ᴳ + φ(1)` on `G` attached to a function `φ` on a
subgroup `H`. -/
private noncomputable def starExt {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (φ : H → ℂ) : G → ℂ :=
  ind H (φ - φ 1 • 1) + φ 1 • 1

private theorem starExt_apply {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (g : G) : starExt H φ g = ind H (φ - φ 1 • 1) g + φ 1 := by
  simp [starExt]

private theorem starExt_conj {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (g h : G) : starExt H φ (h * g * h⁻¹) = starExt H φ g := by
  rw [starExt_apply, starExt_apply, ind_conj]

section Frobenius

variable {G X : Type*} [Group G] [MulAction G X] {x₀ : X} {H : Subgroup G}

private theorem sub_smul_one_conj (φ : H → ℂ) (hφ : ∀ g h, φ (h * g * h⁻¹) = φ g) (g h : H) :
    (φ - φ 1 • 1) (h * g * h⁻¹) = (φ - φ 1 • 1) g := by
  simp [hφ]

private theorem sub_smul_one_one (φ : H → ℂ) : (φ - φ 1 • 1) 1 = 0 := by
  simp

variable [Fintype G]

/-- In a Frobenius action, `φ*` restricts to `φ` on the point stabiliser. -/
private theorem starExt_coe (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (φ : H → ℂ) (hφ : ∀ g h, φ (h * g * h⁻¹) = φ g) (h : H) : starExt H φ h = φ h := by
  rw [starExt_apply, ind_apply_coe hH hfrob _ (sub_smul_one_conj φ hφ) (sub_smul_one_one φ)]
  simp

/-- In a Frobenius action, `φ*` takes the value `φ(1)` at `1` and at every element without fixed
points. -/
private theorem starExt_eq (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀) (φ : H → ℂ) {k : G}
    (hk : k = 1 ∨ ∀ x : X, k • x ≠ x) : starExt H φ k = φ 1 := by
  rw [starExt_apply, ind_apply_eq_zero hH _ (sub_smul_one_one φ) hk, zero_add]

/-- In a Frobenius action, `φ*` has norm `1` when `φ` has norm `1`. -/
private theorem pair_starExt_self [Fintype H] (hH : ∀ g : G, g ∈ H ↔ g • x₀ = x₀)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    (φ : H → ℂ) (hφ : ∀ g h, φ (h * g * h⁻¹) = φ g) (hφφ : pair H φ φ = 1) :
    pair G (starExt H φ) (starExt H φ) = 1 := by
  have hres : (fun h : H => starExt H φ h) = φ := funext (starExt_coe hH hfrob φ hφ)
  have e1 : pair G (ind H (φ - φ 1 • 1)) (starExt H φ) = pair H φ φ - φ 1 * pair H 1 φ := by
    rw [pair_ind H _ _ (starExt_conj H φ), hres, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
  have e2 : pair G 1 (starExt H φ) = pair H φ 1 := by
    rw [pair_comm, starExt, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      pair_ind H _ _ (fun _ _ => rfl), pair_one_one]
    change pair H (φ - φ 1 • 1) 1 + φ 1 • (1 : ℂ) = pair H φ 1
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, pair_one_one]
    simp
  have e3 : ∀ ψ : G → ℂ, pair G (starExt H φ) ψ =
      pair G (ind H (φ - φ 1 • 1)) ψ + φ 1 * pair G 1 ψ := by
    intro ψ
    rw [starExt, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [e3, e1, e2, pair_comm (1 : H → ℂ) φ, hφφ]
  ring

end Frobenius

/-- The pairing of `φ*` with an irreducible character of `G` is an integer, when `φ` is an
irreducible character of `H`. -/
private theorem pair_starExt_charFun_int {G : Type} [Group G] [Fintype G] {H : Subgroup G}
    (c : Irr H) (c' : Irr G) :
    ∃ n : ℤ, pair G (starExt H (Irr.charFun H c)) (Irr.charFun G c') = n := by
  classical
  set V := (Irr.repBundle H c).1
  set W := (Irr.repBundle G c').1
  have hφ : Irr.charFun H c = Representation.character (V.ρ : Representation ℂ H V) :=
    (Irr.charFun_repBundle H c).symm
  have hχ : Irr.charFun G c' = Representation.character (W.ρ : Representation ℂ G W) :=
    (Irr.charFun_repBundle G c').symm
  have hres : (fun h : H => Irr.charFun G c' h) = Representation.character
      ((W.ρ : Representation ℂ G W).comp H.subtype) := by
    rw [hχ]
    rfl
  have hφ1 : Irr.charFun H c 1 = Module.finrank ℂ V := Irr.charFun_one H c
  have e1 : pair G (starExt H (Irr.charFun H c)) (Irr.charFun G c') =
      pair H (Irr.charFun H c) (fun h : H => Irr.charFun G c' h) -
        Irr.charFun H c 1 * pair H 1 (fun h : H => Irr.charFun G c' h) +
        Irr.charFun H c 1 * pair G 1 (Irr.charFun G c') := by
    rw [starExt, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      pair_ind H _ _ (Irr.charFun_classfun G c'), map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
  rw [e1, hres, hφ1, pair_one_character, hχ, pair_one_character, hφ, pair_character_character]
  exact ⟨(Module.finrank ℂ (Representation.IntertwiningMap
      ((W.ρ : Representation ℂ G W).comp H.subtype) (V.ρ : Representation ℂ H V)) : ℤ) -
    (Module.finrank ℂ V : ℤ) * (Module.finrank ℂ (Representation.invariants
      ((W.ρ : Representation ℂ G W).comp H.subtype)) : ℤ) +
    (Module.finrank ℂ V : ℤ) * (Module.finrank ℂ (Representation.invariants
      (W.ρ : Representation ℂ G W)) : ℤ), by push_cast; ring⟩

set_option linter.dupNamespace false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedVariables false in
/-- **Frobenius's theorem on the Frobenius kernel.** Let a finite group $G$ act faithfully and
transitively on a finite set $X$ with at least two elements, such that every point stabiliser is
nontrivial and no nonidentity element of $G$ fixes two distinct points of $X$. Then the set
consisting of the identity together with the elements of $G$ that fix no point of $X$ is a normal
subgroup of $G$.

Source: G. Frobenius, Über auflösbare Gruppen IV, Sitzungsber. Akad. Wiss. Berlin (1901). Via
leanprover/lean-eval@38361be, problem `frobenius_kernel_isNormal`. -/
public theorem frobenius_kernel_isNormal
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} := by
  classical
  obtain ⟨x₀⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, ∀ g : G, g ∈ H ↔ g • x₀ = x₀ :=
    ⟨MulAction.stabilizer G x₀, fun g => MulAction.mem_stabilizer_iff⟩
  have key : ∀ c : Irr H, ∃ c' : Irr G, starExt H (Irr.charFun H c) = Irr.charFun G c' := by
    intro c
    refine exists_charFun_eq _ (starExt_conj H _)
      (pair_starExt_self hH hfrob _ (Irr.charFun_classfun H c) ?_)
      (pair_starExt_charFun_int c) _ (finrank_repBundle_pos c) ?_
    · have := charInner_orth H c c
      rw [ite_eq_left rfl] at this
      exact this
    · rw [starExt_eq hH _ (Or.inl rfl), Irr.charFun_one]
  choose F hF using key
  refine ⟨⨅ c : Irr H, MonoidHom.ker (Irr.repBundle G (F c)).1.ρ,
    Subgroup.normal_iInf_normal fun c => MonoidHom.normal_ker _, ?_⟩
  ext g
  simp only [SetLike.mem_coe, Subgroup.mem_iInf, MonoidHom.mem_ker, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · intro hg
    by_contra hcon
    push Not at hcon
    obtain ⟨hg1, x, hx⟩ := hcon
    obtain ⟨t, rfl⟩ := htrans x₀ x
    have hmem : t⁻¹ * g * t ∈ H := by
      rw [hH, mul_smul, mul_smul, hx, inv_smul_smul]
    have hk : ∀ c : Irr H, (Irr.repBundle G (F c)).1.ρ (t⁻¹ * g * t) = 1 := by
      intro c
      rw [map_mul, map_mul, hg c, mul_one, ← map_mul, inv_mul_cancel, map_one]
    have h1 : (⟨t⁻¹ * g * t, hmem⟩ : H) = 1 := by
      apply eq_one_of_forall_charFun_eq
      intro c
      have hchar : Irr.charFun G (F c) (t⁻¹ * g * t) = Irr.charFun G (F c) 1 := by
        rw [← Irr.charFun_repBundle]
        simp only [FDRep.character, hk c, map_one]
      rw [← hF c] at hchar
      rw [← starExt_coe hH hfrob _ (Irr.charFun_classfun H c),
        ← starExt_coe hH hfrob _ (Irr.charFun_classfun H c) 1]
      exact hchar
    have h2 : t⁻¹ * g * t = 1 := congrArg Subtype.val h1
    apply hg1
    calc g = t * (t⁻¹ * g * t) * t⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · intro hg c
    have h1 : Irr.charFun G (F c) 1 = Irr.charFun H c 1 := by
      rw [← hF c, starExt_eq hH _ (Or.inl rfl)]
    have := (Irr.repBundle G (F c)).2
    apply rho_eq_one_of_character_eq
    · have h2 := Irr.charFun_one G (F c)
      rw [h1, Irr.charFun_one] at h2
      rw [← Nat.cast_inj (R := ℂ).mp h2]
      exact finrank_repBundle_pos c
    · rw [Irr.charFun_repBundle, ← hF c, starExt_eq hH _ hg, starExt_eq hH _ (Or.inl rfl)]

end GroupTheory

end MathlibExt.GroupTheory.FrobeniusWanted
