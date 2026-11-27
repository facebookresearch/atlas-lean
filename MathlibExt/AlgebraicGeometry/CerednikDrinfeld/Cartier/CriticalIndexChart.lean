/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_CriticalIndexChart.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedPiece
public import MathlibExt.RingTheory.MvFormalGroup.Cartier.BaseChange

/-!
# Critical indices and the invariant charts

For a formal `O_D`-module `X`, `FormalODModule.cartierBaseChange` transports Cartier modules
along compatible ring homomorphisms. An index `i` is critical (`CritChart.IsCritical`) when
`ϖ` maps the graded piece `i` into the image of Verschiebung. The file defines the invariants
`CritChart.invariants` (where `ϖ = V`), the elements `CritChart.preInvariants` of the graded
piece `i` where `ϖ = V` up to the image of that piece under `V ^ (2 * n + 1)`
(`CritChart.vPowRange`), their quotients `CritChart.truncInvariants` by the image of the piece
under `V ^ (2 * n)`, and the functoriality of all of these in `B`-algebras.

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes
  de Čerednik et de Drinfeld*, in *Courbes modulaires et courbes de Shimura*, Astérisque
  196–197 (1991), 45–158, for special formal `O_D`-modules and their Cartier modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

section BaseChange

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']
  {B'' : Type w} [CommRing B'']

theorem map_F_map (f : B →+* B') (g : B' →+* B'') (X : FormalODModule p B) :
    (X.map f).F.map g = (X.map (g.comp f)).F :=
  MvFormalGroup.map_map' f g X.F

def cartierBaseChange (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''} (g : B' →+* B'')
    (hg : g.comp f = f') : CartierModule p (X.map f).F →+ CartierModule p (X.map f').F :=
  CartierModule.baseChangeEq g (by rw [map_F, map_F, MvFormalGroup.map_map', hg])

theorem toPowerSeries_cartierBaseChange (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) (l : Fin 2) :
    (X.cartierBaseChange g hg m).toPowerSeries l = MvPowerSeries.map g (m.toPowerSeries l) := rfl

theorem cartierBaseChange_pi (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (endAct (X.map f).varpiEnd m) =
      endAct (X.map f').varpiEnd (X.cartierBaseChange g hg m) := by
  refine CartierModule.baseChangeEq_endAct g _ (fun i => ?_) m
  subst hg
  rfl

theorem cartierBaseChange_act (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (a : Zp2 p) (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (endAct ((X.map f).actEnd a) m) =
      endAct ((X.map f').actEnd a) (X.cartierBaseChange g hg m) := by
  refine CartierModule.baseChangeEq_endAct g _ (fun i => ?_) m
  subst hg
  rfl

theorem cartierBaseChange_verschiebung [CharP B' p] [CharP B'' p] (X : FormalODModule p B)
    {f : B →+* B'} {f' : B →+* B''} (g : B' →+* B'') (hg : g.comp f = f')
    (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (verschiebung m) = verschiebung (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_verschiebung g _ m

theorem cartierBaseChange_verschiebung_iterate [CharP B' p] [CharP B'' p] (X : FormalODModule p B)
    {f : B →+* B'} {f' : B →+* B''} (g : B' →+* B'') (hg : g.comp f = f') (k : ℕ)
    (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg ((⇑(verschiebung (p := p) (Φ := (X.map f).F)))^[k] m) =
      (⇑(verschiebung (p := p) (Φ := (X.map f').F)))^[k] (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_verschiebung_iterate g _ k m

theorem cartierBaseChange_frobenius (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (frobenius m) = frobenius (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_frobenius g _ m

theorem cartierBaseChange_homothety (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (b : B') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (homothety b m) = homothety (g b) (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_homothety g _ b m

theorem cartierBaseChange_smul_witt (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (w : WittVector p B') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (w • m) = (WittVector.map g w) • (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_smul_witt g _ w m

theorem tangent_cartierBaseChange (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) :
    tangent (X.cartierBaseChange g hg m) = fun l => g (tangent m l) :=
  CartierModule.tangent_baseChangeEq g _ m

theorem cartierBaseChange_mem_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) {f : B →+* B'}
    {f' : B →+* B''} (g : B' →+* B'') (hg : g.comp f = f') (i : ℕ)
    {m : CartierModule p (X.map f).F} (hm : m ∈ (X.map f).gradedPiece (f.comp j) i) :
    X.cartierBaseChange g hg m ∈ (X.map f').gradedPiece (f'.comp j) i := by
  intro c
  rw [← cartierBaseChange_act, hm c, cartierBaseChange_homothety]
  congr 1
  rw [map_pow, ← hg]
  rfl

theorem cartierBaseChange_id (X : FormalODModule p B) {f : B →+* B'}
    (h : (RingHom.id B').comp f = f) (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange (RingHom.id B') h m = m :=
  CartierModule.baseChangeEq_id _ m

theorem cartierBaseChange_comp {B₃ : Type*} [CommRing B₃] (X : FormalODModule p B) {f : B →+* B'}
    {f' : B →+* B''} {f'' : B →+* B₃} (g : B' →+* B'') (hg : g.comp f = f') (g' : B'' →+* B₃)
    (hg' : g'.comp f' = f'') (hgg' : (g'.comp g).comp f = f'') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g' hg' (X.cartierBaseChange g hg m) = X.cartierBaseChange
        (g'.comp g) hgg' m :=
  CartierModule.baseChangeEq_baseChangeEq g g' _ _ _ m

theorem cartierBaseChange_injective (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (hinj : Function.Injective g) :
    Function.Injective (X.cartierBaseChange g hg) :=
  CartierModule.baseChangeEq_injective g _ hinj

end BaseChange

namespace CritChart

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

section OneBase

variable [CharP B p]

/-- **Critical index.** For a formal `O_D`-module `X` over a commutative ring `B` of
characteristic `p` and a ring homomorphism `j : Zp2 p →+* B`, an index `i` is critical when the
action of `ϖ` maps the graded piece `i` of the Cartier module into the image of `V`: for every
`m` in the piece there is `g` with `V g = ϖ m`. -/
def IsCritical (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) : Prop :=
  ∀ m ∈ X.gradedPiece j i, ∃ g : CartierModule p X.F, verschiebung g = endAct X.varpiEnd m

/-- **Invariants in degree `i`.** For a formal `O_D`-module `X` over a commutative ring `B` of
characteristic `p` and a ring homomorphism `j : Zp2 p →+* B`, the subgroup of the graded piece
`i` of the Cartier module on which the action of `ϖ` agrees with `V`. -/
def invariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) : AddSubgroup
    (CartierModule p X.F) where
  carrier := {m | m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m = verschiebung m}
  zero_mem' := ⟨zero_mem _, by rw [map_zero, map_zero]⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add, map_add, ha.2, hb.2]⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by rw [map_neg, map_neg, ha.2]⟩

theorem mem_invariants_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (m : CartierModule p X.F) :
    m ∈ invariants X j i ↔ m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m = verschiebung m :=
  Iff.rfl

theorem invariants_le_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    invariants X j i ≤ X.gradedPiece j i := fun _ hm => hm.1

def vPowRange (X : FormalODModule p B) (j : Zp2 p →+* B) (i k : ℕ) : AddSubgroup
    (CartierModule p X.F) where
  carrier := {m | ∃ g ∈ X.gradedPiece j i, (⇑(verschiebung (p := p) (Φ := X.F)))^[k] g = m}
  zero_mem' := ⟨0, zero_mem _, iterate_map_zero _ k⟩
  add_mem' := by
    rintro a b ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', add_mem hg hg', iterate_map_add _ k g g'⟩
  neg_mem' := by
    rintro a ⟨g, hg, rfl⟩
    exact ⟨-g, neg_mem hg, iterate_map_neg _ k g⟩

theorem mem_vPowRange_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i k : ℕ)
    (m : CartierModule p X.F) :
    m ∈ vPowRange X j i k ↔
      ∃ g ∈ X.gradedPiece j i, (⇑(verschiebung (p := p) (Φ := X.F)))^[k] g = m :=
  Iff.rfl

theorem vPowRange_zero (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    vPowRange X j i 0 = X.gradedPiece j i := by
  ext m
  rw [mem_vPowRange_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hm
    exact ⟨m, hm, rfl⟩

theorem iterate_verschiebung_mem_vPowRange (X : FormalODModule p B) (j : Zp2 p →+* B) (i k : ℕ)
    {g : CartierModule p X.F} (hg : g ∈ X.gradedPiece j i) :
    (⇑(verschiebung (p := p) (Φ := X.F)))^[k] g ∈ vPowRange X j i k :=
  ⟨g, hg, rfl⟩

def preInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    AddSubgroup (CartierModule p X.F) where
  carrier :=
      {m | m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m - verschiebung m ∈ vPowRange X j i
          (2 * n + 1)}
  zero_mem' := ⟨zero_mem _, by rw [map_zero, map_zero, sub_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, by
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by
    rw [map_neg, map_neg, ← neg_sub', sub_eq_add_neg]
    exact neg_mem ha.2⟩

theorem mem_preInvariants_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m : CartierModule p X.F) :
    m ∈ preInvariants X j i n ↔
      m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m - verschiebung m ∈ vPowRange X j i (2 * n + 1) :=
  Iff.rfl

theorem invariants_le_preInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    invariants X j i ≤ preInvariants X j i n := fun m hm =>
  ⟨hm.1, by rw [hm.2, sub_self]; exact zero_mem _⟩

theorem preInvariants_le_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    preInvariants X j i n ≤ X.gradedPiece j i := fun _ hm => hm.1

abbrev truncRel (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    AddSubgroup ↥(preInvariants X j i n) :=
  (vPowRange X j i (2 * n)).addSubgroupOf (preInvariants X j i n)

abbrev truncInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) : Type u :=
  ↥(preInvariants X j i n) ⧸ truncRel X j i n

abbrev truncMk (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    ↥(preInvariants X j i n) →+ truncInvariants X j i n :=
  QuotientAddGroup.mk' (truncRel X j i n)

theorem truncMk_surjective (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    Function.Surjective (truncMk X j i n) :=
  QuotientAddGroup.mk'_surjective _

theorem truncMk_eq_zero_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m : ↥(preInvariants X j i n)) :
    truncMk X j i n m = 0 ↔ (m : CartierModule p X.F) ∈ vPowRange X j i (2 * n) := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  rfl

theorem truncMk_eq_truncMk_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m m' : ↥(preInvariants X j i n)) :
    truncMk X j i n m = truncMk X j i n m' ↔ (m : CartierModule p X.F) - m' ∈ vPowRange X j i
        (2 * n) := by
  rw [← sub_eq_zero, ← map_sub, truncMk_eq_zero_iff]
  rfl

theorem truncInvariants_zero_subsingleton (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    Subsingleton (truncInvariants X j i 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := truncMk_surjective X j i 0 a
  obtain ⟨b, rfl⟩ := truncMk_surjective X j i 0 b
  rw [truncMk_eq_truncMk_iff, Nat.mul_zero, vPowRange_zero]
  exact sub_mem a.2.1 b.2.1

def invariantsRed (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    ↥(invariants X j i) →+ truncInvariants X j i n :=
  (truncMk X j i n).comp (AddSubgroup.inclusion (invariants_le_preInvariants X j i n))

theorem invariantsRed_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m : ↥(invariants X j i)) :
    invariantsRed X j i n m = truncMk X j i n
        (AddSubgroup.inclusion (invariants_le_preInvariants X j i n) m) :=
  rfl

end OneBase

section Functor

variable {B₀ : Type u} [CommRing B₀]

abbrev cartierObj (X : FormalODModule p B₀) (B' : Type v) [CommRing B'] [Algebra B₀ B'] : Type v :=
  CartierModule p (X.map (algebraMap B₀ B')).F

abbrev cartierMap (X : FormalODModule p B₀) {B' : Type v} [CommRing B'] [Algebra B₀ B']
    {B'' : Type w}
    [CommRing B''] [Algebra B₀ B''] (φ : B' →ₐ[B₀] B'') : cartierObj X B' →+ cartierObj X B'' :=
  X.cartierBaseChange φ.toRingHom φ.comp_algebraMap

variable {B' : Type v} [CommRing B'] [Algebra B₀ B'] {B'' : Type w} [CommRing B''] [Algebra B₀ B'']

theorem cartierMap_id (X : FormalODModule p B₀) (m : cartierObj X B') : cartierMap X
    (AlgHom.id B₀ B') m = m :=
  X.cartierBaseChange_id _ m

theorem cartierMap_comp (X : FormalODModule p B₀) {B₃ : Type*} [CommRing B₃] [Algebra B₀ B₃]
    (φ : B' →ₐ[B₀] B'') (ψ : B'' →ₐ[B₀] B₃) (m : cartierObj X B') :
    cartierMap X ψ (cartierMap X φ m) = cartierMap X (ψ.comp φ) m :=
  X.cartierBaseChange_comp _ _ _ _ _ m

variable [CharP B' p] [CharP B'' p]

theorem cartierMap_mem_invariants (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ)
    (φ : B' →ₐ[B₀] B'')
    {m : cartierObj X B'}
        (hm : m ∈ invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i) :
    cartierMap X φ m ∈ invariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i := by
  refine ⟨X.cartierBaseChange_mem_gradedPiece j φ.toRingHom φ.comp_algebraMap i hm.1, ?_⟩
  rw [cartierMap, ← cartierBaseChange_pi X φ.toRingHom φ.comp_algebraMap m, hm.2,
    cartierBaseChange_verschiebung X φ.toRingHom φ.comp_algebraMap m]

theorem cartierMap_mem_vPowRange (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i k : ℕ)
    (φ : B' →ₐ[B₀] B'')
    {m : cartierObj X B'}
        (hm : m ∈ vPowRange (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i k) :
    cartierMap X φ m ∈ vPowRange (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i k := by
  obtain ⟨g, hg, rfl⟩ := hm
  exact ⟨cartierMap X φ g, X.cartierBaseChange_mem_gradedPiece j φ.toRingHom φ.comp_algebraMap i hg,
    (X.cartierBaseChange_verschiebung_iterate φ.toRingHom φ.comp_algebraMap k g).symm⟩

theorem cartierMap_mem_preInvariants (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (φ : B' →ₐ[B₀] B'') {m : cartierObj X B'}
    (hm : m ∈ preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) :
    cartierMap X φ m ∈ preInvariants (X.map (algebraMap B₀ B''))
        ((algebraMap B₀ B'').comp j) i n := by
  refine ⟨X.cartierBaseChange_mem_gradedPiece j φ.toRingHom φ.comp_algebraMap i hm.1, ?_⟩
  have h := cartierMap_mem_vPowRange X j i (2 * n + 1) φ hm.2
  rwa [cartierMap, map_sub, cartierBaseChange_pi X φ.toRingHom φ.comp_algebraMap m,
    cartierBaseChange_verschiebung X φ.toRingHom φ.comp_algebraMap m] at h

def invariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ) (φ : B' →ₐ[B₀] B'') :
    ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i) →+
      ↥(invariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i) :=
  ((cartierMap X φ).comp (AddSubgroup.subtype _)).codRestrict _
    fun m => cartierMap_mem_invariants X j i φ m.2

@[simp] theorem coe_invariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ)
    (φ : B' →ₐ[B₀] B'')
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    (invariantsMap X j i φ m : cartierObj X B'') = cartierMap X φ m := rfl

def preInvariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'') :
    ↥(preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) →+
      ↥(preInvariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i n) :=
  ((cartierMap X φ).comp (AddSubgroup.subtype _)).codRestrict _
    fun m => cartierMap_mem_preInvariants X j i n φ m.2

@[simp] theorem coe_preInvariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (φ : B' →ₐ[B₀] B'')
        (m : ↥(preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n)) :
    (preInvariantsMap X j i n φ m : cartierObj X B'') = cartierMap X φ m := rfl

def truncMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'') :
    truncInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n →+
      truncInvariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i n :=
  QuotientAddGroup.map _ _ (preInvariantsMap X j i n φ) fun _ hm =>
    cartierMap_mem_vPowRange X j i (2 * n) φ hm

theorem truncMap_truncMk (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'')
    (m₀ : ↥(preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n)) :
    truncMap X j i n φ (truncMk _ _ i n m₀) = truncMk _ _ i n (preInvariantsMap X j i n φ m₀) :=
  rfl

theorem truncMap_invariantsRed (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (φ : B' →ₐ[B₀] B'')
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    truncMap X j i n φ (invariantsRed _ _ i n m) = invariantsRed _ _ i n
        (invariantsMap X j i φ m) :=
  rfl

omit [CharP B'' p] in
theorem invariantsMap_id (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ)
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    invariantsMap X j i (AlgHom.id B₀ B') m = m :=
  Subtype.ext (cartierMap_id X m.1)

theorem invariantsMap_comp (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ) {B₃ : Type*}
    [CommRing B₃] [Algebra B₀ B₃] [CharP B₃ p] (φ : B' →ₐ[B₀] B'') (ψ : B'' →ₐ[B₀] B₃)
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    invariantsMap X j i ψ (invariantsMap X j i φ m) = invariantsMap X j i (ψ.comp φ) m :=
  Subtype.ext (cartierMap_comp X φ ψ m.1)

omit [CharP B'' p] in
theorem truncMap_id (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (x : truncInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) :
    truncMap X j i n (AlgHom.id B₀ B') x = x := by
  obtain ⟨m, rfl⟩ := truncMk_surjective _ _ i n x
  exact (truncMap_truncMk X j i n _ m).trans (congrArg _ (Subtype.ext (cartierMap_id X m.1)))

theorem truncMap_comp (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) {B₃ : Type*}
    [CommRing B₃] [Algebra B₀ B₃] [CharP B₃ p] (φ : B' →ₐ[B₀] B'') (ψ : B'' →ₐ[B₀] B₃)
    (x : truncInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) :
    truncMap X j i n ψ (truncMap X j i n φ x) = truncMap X j i n (ψ.comp φ) x := by
  obtain ⟨m, rfl⟩ := truncMk_surjective _ _ i n x
  exact congrArg (truncMk _ _ i n) (Subtype.ext (cartierMap_comp X φ ψ m.1))

end Functor

section Transition

variable [CharP B p]

theorem preInvariants_succ_le (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (hV : ∀ g ∈ X.gradedPiece j i, verschiebung (verschiebung g) ∈ X.gradedPiece j i) :
    preInvariants X j i (n + 1) ≤ preInvariants X j i n := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  obtain ⟨g, hg, hgm⟩ := hm.2
  refine ⟨verschiebung (verschiebung g), hV g hg, ?_⟩
  rw [← hgm, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring,
    Function.iterate_add_apply (⇑(verschiebung (p := p) (Φ := X.F))) (2 * n + 1) 2 g]
  rfl

theorem vPowRange_succ_le (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (hV : ∀ g ∈ X.gradedPiece j i, verschiebung (verschiebung g) ∈ X.gradedPiece j i) :
    vPowRange X j i (2 * (n + 1)) ≤ vPowRange X j i (2 * n) := by
  rintro m ⟨g, hg, hgm⟩
  refine ⟨verschiebung (verschiebung g), hV g hg, ?_⟩
  rw [← hgm, show 2 * (n + 1) = 2 * n + 2 by ring,
    Function.iterate_add_apply (⇑(verschiebung (p := p) (Φ := X.F))) (2 * n) 2 g]
  rfl

def truncTransition (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (hV : ∀ g ∈ X.gradedPiece j i, verschiebung (verschiebung g) ∈ X.gradedPiece j i) :
    truncInvariants X j i (n + 1) →+ truncInvariants X j i n :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion (preInvariants_succ_le X j i n hV))
    fun _ hm => vPowRange_succ_le X j i n hV hm

end Transition

end CritChart

end FormalODModule

end CerednikDrinfeld

end
