/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Order.Atoms.Finite
import MathlibExt.Combinatorics.SimpleGraph.Frucht

/-!
# Every finite group as an outer automorphism group (Kourovka Notebook Problem 16.59)

We prove that every finite group is isomorphic to the outer automorphism group of a finite group.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.59 (D.
MacHale). UnsolvedMath record UM-00701251 (`KOU-16.59`), dataset ulamai/UnsolvedMath v1.8.0.

`K ≅ Aut G / Inn G` is stated as a surjective homomorphism `Aut G → K` whose kernel is the group of
inner automorphisms (the range of `MulAut.conj`), equivalent by the first isomorphism theorem.

The proof uses Frucht's theorem and two finite direct powers of the alternating group on five
letters. Automorphisms of a direct power permute its simple factors. For any subgroup of the
automorphism group containing the inner automorphisms, restriction of conjugation identifies its
normalizer with its own automorphism group.

For a finite graph, take families of subgroups indexed by the vertices. The entries are maximal
proper subgroups at the vertices of a singleton or of an edge, and the whole group elsewhere.
Coordinatewise automorphisms act faithfully on these families. Point stabilizers recover both the
entries and their supports. The permutation normalizer therefore acts on the graph, and its kernel
is the coordinatewise action. Taking the preimage of that action under the factor permutation
homomorphism for the second direct power yields the group realizing the graph automorphism group.
-/

namespace MathlibExt.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59Wanted

@[expose] public section

/-- **Kourovka Problem 16.59 (finite groups as outer automorphism groups).** The statement that
for every finite group $K$ there are a finite group $G$ and a surjective homomorphism
$\mathrm{Aut}(G) \to K$ whose kernel is the group $\mathrm{Inn}(G)$ of inner automorphisms of
$G$, that is, $K$ is isomorphic to $\mathrm{Out}(G) = \mathrm{Aut}(G) / \mathrm{Inn}(G)$. -/
def everyFiniteGroupIsOuterAutomorphismGroup : Prop :=
  ∀ (K : Type) [Group K] [Finite K], ∃ (G : Type) (_ : Group G) (_ : Finite G)
    (φ : MulAut G →* K), Function.Surjective φ ∧ φ.ker = (MulAut.conj : G →* MulAut G).range

end

noncomputable section

open Function
open scoped commutatorElement

variable {S I : Type} [Group S] [IsSimpleGroup S]

section CoordinateFactors

variable [DecidableEq I]

private def factor (S : Type) [Group S] (i : I) : Subgroup (I → S) :=
  (MonoidHom.mulSingle (fun _ : I => S) i).range

omit [IsSimpleGroup S] in
private theorem mem_factor_iff (i : I) (x : I → S) :
    x ∈ factor S i ↔ ∀ j ≠ i, x j = 1 := by
  constructor
  · rintro ⟨s, rfl⟩ j hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · intro h
    refine ⟨x i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simpa [Pi.mulSingle_eq_of_ne hj] using (h j hj).symm

omit [IsSimpleGroup S] in
private theorem factor_normal (i : I) : (factor S i).Normal where
  conj_mem x hx g := (mem_factor_iff i _).mpr fun j hj => by
    simp [(mem_factor_iff i x).mp hx j hj]

private theorem factor_injective : Injective (factor (I := I) S) := by
  intro i j heq
  by_contra h
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hsi : Pi.mulSingle i s ∈ factor S i := ⟨s, rfl⟩
  rw [heq] at hsi
  exact hs (by simpa using (mem_factor_iff j _).mp hsi i h)

private theorem factor_le_of_apply_ne_one (hz : Subgroup.center S = ⊥)
    (N : Subgroup (I → S)) [N.Normal] {x : I → S} (hx : x ∈ N) {i : I}
    (hxi : x i ≠ 1) : factor S i ≤ N := by
  let σ := MonoidHom.mulSingle (fun _ : I => S) i
  have hc : (N.comap σ).Normal := inferInstance
  suffices hh : N.comap σ = ⊤ by
    rintro _ ⟨s, rfl⟩
    exact show s ∈ N.comap σ by rw [hh]; trivial
  apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap σ)).resolve_left
  intro hb
  have hcenter : x i ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hm : ⁅x i, s⁆ ∈ N.comap σ := by
      change σ ⁅x i, s⁆ ∈ N
      have he : σ ⁅x i, s⁆ = ⁅x, σ s⁆ := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [σ, commutatorElement_def]
        · simp [σ, Pi.mulSingle_eq_of_ne hj, commutatorElement_def]
      rw [he, commutatorElement_def, mul_assoc x (σ s) x⁻¹, mul_assoc x (σ s * x⁻¹) (σ s)⁻¹]
      exact N.mul_mem hx ((inferInstance : N.Normal).conj_mem _ (N.inv_mem hx) _)
    rw [hb, Subgroup.mem_bot] at hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm
  exact hxi (by simpa [hz] using hcenter)

private theorem normal_eq_factor_of_simple (hz : Subgroup.center S = ⊥)
    (N : Subgroup (I → S)) [N.Normal] [IsSimpleGroup N] : ∃ i, N = factor S i := by
  obtain ⟨x, hx⟩ := exists_ne (1 : N)
  have hne : ∃ i, (x : I → S) i ≠ 1 := by
    by_contra! h
    exact hx (Subtype.ext (funext h))
  obtain ⟨i, hi⟩ := hne
  have hle : factor S i ≤ N := factor_le_of_apply_ne_one hz N x.property hi
  have := factor_normal (S := S) i
  have htop : (factor S i).subgroupOf N = ⊤ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left
    intro hb
    have hm : (⟨Pi.mulSingle i (x.val i), hle ⟨x.val i, rfl⟩⟩ : N) ∈
        (factor S i).subgroupOf N := ⟨x.val i, rfl⟩
    rw [hb, Subgroup.mem_bot] at hm
    exact hi (by simpa using congrArg (fun y : N => y.val i) hm)
  exact ⟨i, hle.antisymm' fun y hy =>
    show (⟨y, hy⟩ : N) ∈ (factor S i).subgroupOf N from by rw [htop]; trivial⟩

private theorem map_factor (hz : Subgroup.center S = ⊥)
    (a : MulAut (I → S)) (i : I) : ∃ j, (factor S i).map a.toMonoidHom = factor S j := by
  have := factor_normal (S := S) i
  have : IsSimpleGroup (factor S i) :=
    (MonoidHom.ofInjective (f := MonoidHom.mulSingle (fun _ : I => S) i)
      (Pi.mulSingle_injective (M := fun _ : I => S) i)).symm.isSimpleGroup
  have := Subgroup.Normal.map (H := factor S i) inferInstance a.toMonoidHom a.surjective
  have : IsSimpleGroup ((factor S i).map a.toMonoidHom) :=
    (a.subgroupMap (factor S i)).symm.isSimpleGroup
  exact normal_eq_factor_of_simple hz _

private def coordFun (hz : Subgroup.center S = ⊥) (a : MulAut (I → S)) (i : I) : I :=
  (map_factor hz a i).choose

private theorem map_factor_eq (hz : Subgroup.center S = ⊥)
    (a : MulAut (I → S)) (i : I) :
    (factor S i).map a.toMonoidHom = factor S (coordFun hz a i) :=
  (map_factor hz a i).choose_spec

private theorem coordFun_one (hz : Subgroup.center S = ⊥) (i : I) :
    coordFun hz (1 : MulAut (I → S)) i = i := by
  apply factor_injective (S := S)
  rw [← map_factor_eq]
  exact Subgroup.map_id _

private theorem coordFun_mul (hz : Subgroup.center S = ⊥)
    (a b : MulAut (I → S)) (i : I) :
    coordFun hz (a * b) i = coordFun hz a (coordFun hz b i) := by
  apply factor_injective (S := S)
  rw [← map_factor_eq, ← map_factor_eq, ← map_factor_eq, Subgroup.map_map]
  rfl

private def coords (hz : Subgroup.center S = ⊥) : MulAut (I → S) →* Equiv.Perm I where
  toFun a :=
    { toFun := coordFun hz a
      invFun := coordFun hz a⁻¹
      left_inv := fun i => by rw [← coordFun_mul, inv_mul_cancel, coordFun_one]
      right_inv := fun i => by rw [← coordFun_mul, mul_inv_cancel, coordFun_one] }
  map_one' := Equiv.ext (coordFun_one hz)
  map_mul' a b := Equiv.ext (coordFun_mul hz a b)

private def reindex (e : Equiv.Perm I) : MulAut (I → S) where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_mul' _ _ := rfl

private theorem coords_reindex (hz : Subgroup.center S = ⊥) (e : Equiv.Perm I) :
    coords hz (reindex (S := S) e) = e := by
  ext i
  change coordFun hz (reindex e) i = e i
  apply factor_injective (S := S)
  rw [← map_factor_eq]
  ext x
  rw [Subgroup.mem_map_equiv, mem_factor_iff, mem_factor_iff]
  change (∀ j ≠ i, x (e j) = 1) ↔ ∀ j ≠ e i, x j = 1
  exact ⟨fun h j hj => by simpa using h (e.symm j) (fun he => hj (by simp [← he])),
    fun h j hj => h (e j) (e.injective.ne hj)⟩

private theorem coords_conj (hz : Subgroup.center S = ⊥) (x : I → S) :
    coords hz (MulAut.conj x) = 1 := by
  ext i
  change coordFun hz (MulAut.conj x) i = i
  apply factor_injective (S := S)
  rw [← map_factor_eq]
  have := factor_normal (S := S) i
  exact Subgroup.Normal.map_conj_eq _ x

end CoordinateFactors

section Characteristic

variable [Finite I]

variable {L : Type} [Group L]

omit [Finite I] in
private theorem normal_inter_centralizer_eq_bot (hz : Subgroup.center S = ⊥)
    (f : (I → S) →* L) (hf : Injective f) (M : Subgroup L) [M.Normal]
    (hM : M ≤ f.range) : M ⊓ Subgroup.centralizer (M : Set L) = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  rintro z ⟨hzM, hzc⟩
  obtain ⟨x, rfl⟩ := hM hzM
  have hx : x ∈ M.comap f := hzM
  have he : x = 1 := by
    funext i
    by_contra hi
    have hfac := factor_le_of_apply_ne_one hz (M.comap f) hx hi
    have hzi : x i ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      have hmem : f (Pi.mulSingle i s) ∈ M := hfac ⟨s, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.mp hzc _ hmem
      have heq : Pi.mulSingle i s * x = x * Pi.mulSingle i s :=
        hf (by simpa only [map_mul] using hc)
      simpa using congrFun heq i
    exact hi (by simpa [hz] using hzi)
  simp [he]

-- The intersection with P and its centralizer together account for all coordinate factors.
-- The centralizer part is normal and disjoint from P, so it is trivial.
private theorem range_le_of_centralizer_eq_bot (hz : Subgroup.center S = ⊥)
    (f : (I → S) →* L) (hf : Injective f) [f.range.Normal]
    (P : Subgroup L) [P.Normal] (hP : Subgroup.centralizer (P : Set L) = ⊥) :
    f.range ≤ P := by
  classical
  let M := f.range ⊓ P
  let T := f.range ⊓ Subgroup.centralizer (M : Set L)
  have hT : T = ⊥ := by
    have hn : T.Normal := inferInstanceAs ((f.range ⊓ Subgroup.centralizer (M : Set L)).Normal)
    have hd : Disjoint T P := by
      rw [disjoint_iff]
      calc
        T ⊓ P = M ⊓ Subgroup.centralizer (M : Set L) := inf_right_comm ..
        _ = ⊥ := normal_inter_centralizer_eq_bot hz f hf M inf_le_left
    have hc : ⁅T, P⁆ = ⊥ := le_antisymm
      ((Subgroup.commutator_le_inf (H₁ := T) (H₂ := P)).trans hd.le_bot) bot_le
    exact le_antisymm ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans_eq hP) bot_le
  rintro z ⟨x, rfl⟩
  change x ∈ P.comap f
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro i
  by_contra hi
  have hxi : x i ≠ 1 := by
    intro he
    exact hi (by simp [he])
  have hzero (y : I → S) (hy : f y ∈ M) : y i = 1 := by
    by_contra hne
    have hfac := factor_le_of_apply_ne_one hz (M.comap f) (show y ∈ M.comap f from hy) hne
    exact hi (hfac (show Pi.mulSingle i (x i) ∈ factor S i from ⟨x i, rfl⟩)).2
  have hmem : f (Pi.mulSingle i (x i)) ∈ T := by
    refine ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain ⟨v, rfl⟩ := hy.1
    rw [← map_mul, ← map_mul]
    congr 1
    funext j
    change v j * Pi.mulSingle (M := fun _ : I => S) i (x i) j =
      Pi.mulSingle (M := fun _ : I => S) i (x i) j * v j
    by_cases hji : j = i
    · subst j
      simp [hzero v hy]
    · simp [Pi.mulSingle_eq_of_ne hji]
  rw [hT, Subgroup.mem_bot, ← map_one f] at hmem
  exact hxi (by simpa using congrFun (hf hmem) i)

private theorem conjugate_conj {B : Type} [Group B] (a : MulAut B) (x : B) :
    a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
  ext y
  change a (x * a.symm y * x⁻¹) = a x * y * (a x)⁻¹
  simp

omit [IsSimpleGroup S] [Finite I] in
private theorem conj_pi_injective (hz : Subgroup.center S = ⊥) :
    Injective (MulAut.conj : (I → S) →* MulAut (I → S)) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : MulAut.conj x = 1 := hx
  apply Subgroup.mem_bot.mpr
  funext i
  have hcenter : x i ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have he := congrArg (fun e : MulAut (I → S) => e (Pi.mulSingle i s) i) hx'
    change (x * Pi.mulSingle (M := fun _ : I => S) i s * x⁻¹) i =
      Pi.mulSingle (M := fun _ : I => S) i s i at he
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  simpa [hz] using hcenter

omit [IsSimpleGroup S] [Finite I] in
private theorem eq_of_commutes_inn (hz : Subgroup.center S = ⊥)
    (a : MulAut (I → S)) (ha : ∀ x : I → S, MulAut.conj x * a = a * MulAut.conj x) :
    a = 1 := by
  apply DFunLike.ext
  intro x
  change a x = x
  apply conj_pi_injective hz
  rw [← conjugate_conj, ← ha, mul_inv_cancel_right]

private def embeddedInn (D : Subgroup (MulAut (I → S)))
    (hD : (MulAut.conj (G := I → S)).range ≤ D) : (I → S) →* D :=
  (MulAut.conj (G := I → S)).codRestrict D fun x => hD ⟨x, rfl⟩

private theorem embeddedInn_characteristic (hz : Subgroup.center S = ⊥)
    (D : Subgroup (MulAut (I → S))) (hD : (MulAut.conj (G := I → S)).range ≤ D) :
    (embeddedInn D hD).range.Characteristic := by
  let f := embeddedInn D hD
  have hf : Injective f := fun _ _ h => conj_pi_injective hz (congrArg Subtype.val h)
  have hfn : f.range.Normal := ⟨by
    rintro _ ⟨x, rfl⟩ d
    exact ⟨d.val x, Subtype.ext (conjugate_conj d.val x).symm⟩⟩
  have hc : Subgroup.centralizer (f.range : Set D) = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact eq_of_commutes_inn hz a.val fun x =>
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp ha (f x) ⟨x, rfl⟩)
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro a
  have hP : (f.range.comap a.toMonoidHom).Normal := inferInstance
  refine range_le_of_centralizer_eq_bot hz f hf _ ?_
  apply le_antisymm _ bot_le
  intro y hy
  have hya : a y ∈ Subgroup.centralizer (f.range : Set D) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      congrArg a (Subgroup.mem_centralizer_iff.mp hy (a.symm x)
        (show a (a.symm x) ∈ f.range by simpa using hx))
  rw [hc, Subgroup.mem_bot] at hya
  exact Subgroup.mem_bot.mpr (a.injective (hya.trans a.map_one.symm))

end Characteristic

section Overgroups

variable [Finite I]

private abbrev norm {A : Type} [Group A] (H : Subgroup A) :=
  Subgroup.normalizer (H : Set A)

-- Restrict an automorphism of D to the characteristic copy of the direct power.
-- Conjugation by that restriction recovers the original automorphism of D.
private theorem normalizerAut_bijective (hz : Subgroup.center S = ⊥)
    (D : Subgroup (MulAut (I → S))) (hD : (MulAut.conj (G := I → S)).range ≤ D) :
    Bijective D.normalizerMonoidHom := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.normalizerMonoidHom_ker]
    apply le_antisymm _ bot_le
    intro a ha
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact eq_of_commutes_inn hz a.val fun x =>
      Subgroup.mem_centralizer_iff.mp ha _ (hD ⟨x, rfl⟩)
  · intro b
    let f := embeddedInn D hD
    have hf : Injective f := fun _ _ h => conj_pi_injective hz (congrArg Subtype.val h)
    have hb : f.range.map b.toMonoidHom = f.range :=
      Subgroup.characteristic_iff_map_eq.mp (embeddedInn_characteristic hz D hD) b
    let e : (I → S) ≃* f.range := MonoidHom.ofInjective hf
    let a : MulAut (I → S) :=
      e.trans ((b.subgroupMap f.range).trans ((MulEquiv.subgroupCongr hb).trans e.symm))
    have hcomp (x : I → S) : b (f x) = f (a x) := by
      have he := congrArg Subtype.val (e.apply_symm_apply
        ((b.subgroupMap f.range).trans (MulEquiv.subgroupCongr hb) (e x)))
      exact he.symm
    have hact (d : D) (x : I → S) : d * f x * d⁻¹ = f (d.val x) :=
      Subtype.ext (conjugate_conj d.val x)
    have hpoint (d : D) (x : I → S) : (b d).val (a x) = a (d.val x) := by
      apply hf
      rw [← hact, ← hcomp, ← map_inv, ← map_mul, ← map_mul, hact, hcomp]
    have hconj (d : D) : a * d.val * a⁻¹ = (b d).val := by
      apply DFunLike.ext
      intro x
      change a (d.val (a.symm x)) = (b d).val x
      simpa using (hpoint d (a.symm x)).symm
    have ha : a ∈ (norm D) := by
      apply Subgroup.mem_normalizer_iff.mpr
      intro d
      refine ⟨fun hd => ?_, fun hd => ?_⟩
      · rw [hconj ⟨d, hd⟩]
        exact (b ⟨d, hd⟩).property
      · obtain ⟨d', hd'⟩ := b.surjective ⟨a * d * a⁻¹, hd⟩
        have he : a * d'.val * a⁻¹ = a * d * a⁻¹ :=
          (hconj d').trans (congrArg Subtype.val hd')
        have hdval : d'.val = d := mul_left_cancel (mul_right_cancel he)
        exact hdval ▸ d'.property
    refine ⟨⟨a, ha⟩, DFunLike.ext _ _ fun d => ?_⟩
    exact Subtype.ext (hconj d)

private def normalizerAut (hz : Subgroup.center S = ⊥)
    (D : Subgroup (MulAut (I → S))) (hD : (MulAut.conj (G := I → S)).range ≤ D) :
    (norm D) ≃* MulAut D :=
  MulEquiv.ofBijective D.normalizerMonoidHom (normalizerAut_bijective hz D hD)

private theorem normalizerAut_inner (hz : Subgroup.center S = ⊥)
    (D : Subgroup (MulAut (I → S))) (hD : (MulAut.conj (G := I → S)).range ≤ D) (d : D) :
    normalizerAut hz D hD ⟨d.val, D.le_normalizer d.property⟩ = MulAut.conj d := by
  rfl

private theorem outer_realize {B K : Type} [Group B] [Group K] [Finite S]
    (hz : Subgroup.center S = ⊥) (p : MulAut (I → S) →* B) (hp : Surjective p)
    (hpInn : ∀ x : I → S, p (MulAut.conj x) = 1)
    (H : Subgroup B) (q : (norm H) →* K) (hq : Surjective q)
    (hk : q.ker = H.subgroupOf (norm H)) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G)
      (φ : MulAut G →* K), Surjective φ ∧ φ.ker = (MulAut.conj : G →* MulAut G).range := by
  let D := H.comap p
  have hD : (MulAut.conj (G := I → S)).range ≤ D := by
    rintro _ ⟨x, rfl⟩
    change p (MulAut.conj x) ∈ H
    rw [hpInn]; exact H.one_mem
  let e := normalizerAut hz D hD
  have hn : norm D = (norm H).comap p :=
    (Subgroup.comap_normalizer_eq_of_surjective H hp).symm
  let n : (norm D) →* (norm H) :=
    (p.comp (norm D).subtype).codRestrict _ fun x => by
      change x.val ∈ (norm H).comap p
      rw [← hn]; exact x.property
  have hnSurj : Surjective n := by
    intro x
    obtain ⟨a, ha⟩ := hp x.val
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    rw [hn]
    change p a ∈ (norm H)
    rw [ha]; exact x.property
  refine ⟨D, inferInstance, inferInstance, q.comp (n.comp e.symm.toMonoidHom),
    hq.comp (hnSurj.comp e.symm.surjective), ?_⟩
  ext a
  obtain ⟨b, rfl⟩ := e.surjective a
  change q (n (e.symm (e b))) = 1 ↔ _
  rw [e.symm_apply_apply]
  change n b ∈ q.ker ↔ _
  rw [hk]
  change b.val ∈ D ↔ e b ∈ MulAut.conj.range
  constructor
  · intro hb
    exact ⟨⟨b.val, hb⟩, (normalizerAut_inner hz D hD ⟨b.val, hb⟩).symm⟩
  · rintro ⟨d, hd⟩
    have he : e ⟨d.val, D.le_normalizer d.property⟩ = e b :=
      (normalizerAut_inner hz D hD d).trans hd
    have hb := congrArg Subtype.val (e.injective he)
    exact hb ▸ d.property

end Overgroups

section Graph

variable [DecidableEq I]

variable (hz : Subgroup.center S = ⊥)

private abbrev Fixing := (coords (I := I) hz).ker

private theorem inn_le_fixing : (MulAut.conj (G := I → S)).range ≤ Fixing hz := by
  rintro _ ⟨x, rfl⟩
  exact coords_conj hz x

private theorem fixingSingle (h : Fixing (I := I) hz) (i : I) (s : S) :
    h.val (Pi.mulSingle i s) = Pi.mulSingle i (h.val (Pi.mulSingle i s) i) := by
  have hh : coords hz h.val = 1 := h.property
  have he : coordFun hz h.val i = i := congrArg (fun e : Equiv.Perm I => e i) hh
  have hx : h.val (Pi.mulSingle i s) ∈ factor S i := by
    rw [← (map_factor_eq hz h.val i).trans (congrArg (factor S) he)]
    exact Subgroup.mem_map_of_mem _ ⟨s, rfl⟩
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Pi.mulSingle_eq_of_ne hj, (mem_factor_iff i _).mp hx j hj]

private def localAut (i : I) : Fixing (I := I) hz →* MulAut S where
  toFun h :=
    { toFun := fun s => h.val (Pi.mulSingle i s) i
      invFun := fun s => h⁻¹.val (Pi.mulSingle i s) i
      left_inv := fun s => by
        change h.val.symm (Pi.mulSingle i (h.val (Pi.mulSingle i s) i)) i = s
        rw [← fixingSingle hz h, MulEquiv.symm_apply_apply, Pi.mulSingle_eq_same]
      right_inv := fun s => by
        change h.val (Pi.mulSingle i (h⁻¹.val (Pi.mulSingle i s) i)) i = s
        rw [← fixingSingle hz h⁻¹]
        change h.val (h.val.symm (Pi.mulSingle i s)) i = s
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]
      map_mul' := fun s t => by
        change h.val ((MonoidHom.mulSingle (fun _ : I => S) i) (s * t)) i = _
        rw [map_mul, map_mul]
        rfl }
  map_one' := by
    ext s
    exact Pi.mulSingle_eq_same (M := fun _ : I => S) i s
  map_mul' a b := DFunLike.ext _ _ fun s => by
    change a.val (b.val (Pi.mulSingle i s)) i =
      a.val (Pi.mulSingle i (b.val (Pi.mulSingle i s) i)) i
    rw [← fixingSingle hz b]

private theorem localAut_apply (h : Fixing (I := I) hz) (i : I) (s : S) :
    localAut hz i h s = h.val (Pi.mulSingle i s) i := rfl

private theorem localAut_inn (x : I → S) (i : I) :
    localAut hz i (embeddedInn (Fixing hz) (inn_le_fixing hz) x) = MulAut.conj (x i) := by
  apply DFunLike.ext
  intro s
  simp [localAut_apply, embeddedInn, MulAut.conj_apply]

private def graphSupport (Γ : SimpleGraph I) (T : Set I) : Prop :=
  (∃ i, T = {i}) ∨ ∃ i j, Γ.Adj i j ∧ T = {i, j}

private def supportOf (f : I → Subgroup S) : Set I := {i | f i ≠ ⊤}

private def GraphPoints (S : Type) [Group S] (Γ : SimpleGraph I) :=
  {f : I → Subgroup S // (∀ i, f i = ⊤ ∨ IsCoatom (f i)) ∧ graphSupport Γ (supportOf f)}

private instance graphPointsFinite [Finite I] [Finite S] (Γ : SimpleGraph I) :
    Finite (GraphPoints S Γ) :=
  Finite.of_injective
    (fun x : GraphPoints S Γ => fun i => (x.val i : Set S))
    (fun _ _ h => Subtype.ext (funext fun i => SetLike.coe_injective (congrFun h i)))

variable (Γ : SimpleGraph I)

omit [IsSimpleGroup S] [DecidableEq I] in
private theorem supportOf_map (a : I → MulAut S) (f : I → Subgroup S) :
    supportOf (fun i => (a i).mapSubgroup (f i)) = supportOf f := by
  ext i
  change (a i).mapSubgroup (f i) ≠ ⊤ ↔ f i ≠ ⊤
  calc
    _ ↔ (a i).mapSubgroup (f i) ≠ (a i).mapSubgroup ⊤ := by rw [map_top]
    _ ↔ _ := (a i).mapSubgroup.injective.ne_iff

private def mapPoint (a : I → MulAut S) (x : GraphPoints S Γ) : GraphPoints S Γ :=
  ⟨fun i => (a i).mapSubgroup (x.val i), fun i => by
    rcases x.property.1 i with hi | hi
    · left
      simp [hi]
    · right
      exact ((a i).mapSubgroup.isCoatom_iff _).mpr hi,
    by rw [supportOf_map]; exact x.property.2⟩

omit [IsSimpleGroup S] [DecidableEq I] in
private theorem mapPoint_mul (a b : I → MulAut S) (x : GraphPoints S Γ) :
    mapPoint Γ (a * b) x = mapPoint Γ a (mapPoint Γ b x) := by
  apply Subtype.ext
  funext i
  change (x.val i).map ((a i * b i).toMonoidHom) =
    ((x.val i).map (b i).toMonoidHom).map (a i).toMonoidHom
  rw [Subgroup.map_map]
  rfl

omit [IsSimpleGroup S] [DecidableEq I] in
private theorem mapPoint_one (x : GraphPoints S Γ) :
    mapPoint Γ (1 : I → MulAut S) x = x := by
  apply Subtype.ext
  funext i
  exact Subgroup.map_id _

private def graphAction : Fixing (I := I) hz →* Equiv.Perm (GraphPoints S Γ) where
  toFun h :=
    { toFun := mapPoint Γ (fun i => localAut hz i h)
      invFun := mapPoint Γ (fun i => localAut hz i h⁻¹)
      left_inv := fun x => by
        rw [← mapPoint_mul, show (fun i => localAut hz i h⁻¹) *
          (fun i => localAut hz i h) = 1 by funext i; simp, mapPoint_one]
      right_inv := fun x => by
        rw [← mapPoint_mul, show (fun i => localAut hz i h) *
          (fun i => localAut hz i h⁻¹) = 1 by funext i; simp, mapPoint_one] }
  map_one' := Equiv.ext fun x => by
    change mapPoint Γ (fun i => localAut hz i 1) x = x
    simp only [map_one]
    exact mapPoint_one Γ x
  map_mul' a b := Equiv.ext fun x => by
    change mapPoint Γ (fun i => localAut hz i (a * b)) x =
      mapPoint Γ (fun i => localAut hz i a) (mapPoint Γ (fun i => localAut hz i b) x)
    simp only [map_mul]
    exact mapPoint_mul Γ _ _ x

private theorem coatom_normalizer (hcS : Subgroup.center S = ⊥) (P : Subgroup S) (hP : IsCoatom P) :
    norm P = P := by
  have hb : P ≠ ⊥ := by
    intro he
    have hc : IsCyclic S := by
      obtain ⟨a, ha⟩ := exists_ne (1 : S)
      have hx : P < Subgroup.zpowers a :=
        lt_of_le_of_ne (he.symm ▸ bot_le) (fun he' => ha (by
          have hm := Subgroup.mem_zpowers a
          rw [← he', he, Subgroup.mem_bot] at hm
          exact hm))
      have ht := hP.2 _ hx
      exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, ht⟩
    have := hc
    have hcomm : IsMulCommutative S := inferInstance
    have htop := Subgroup.center_eq_top_iff.mpr hcomm
    have hne := bot_ne_top (α := Subgroup S)
    exact hne (hcS.symm.trans htop)
  by_contra! hne
  have ht := hP.2 _ (lt_of_le_of_ne P.le_normalizer (Ne.symm hne))
  have hn := Subgroup.normalizer_eq_top_iff.mp ht
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal P).elim hb hP.1

-- The stabilizer in the i-th simple factor recovers the subgroup stored at i.
private theorem point_fixed_iff (x : GraphPoints S Γ) (i : I) (s : S) :
    graphAction hz Γ
      (embeddedInn (Fixing hz) (inn_le_fixing hz) (Pi.mulSingle i s)) x = x ↔
        s ∈ x.val i := by
  change mapPoint Γ (fun j => localAut hz j
    (embeddedInn (Fixing hz) (inn_le_fixing hz) (Pi.mulSingle i s))) x = x ↔ _
  simp only [localAut_inn]
  have hii : (x.val i).map (MulAut.conj s) = x.val i ↔ s ∈ x.val i := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
    rcases x.property.1 i with h | h
    · rw [h]
      exact iff_of_true (Subgroup.le_normalizer (Subgroup.mem_top s)) (Subgroup.mem_top s)
    · exact Eq.to_iff (congrArg (fun P : Subgroup S => s ∈ P) (coatom_normalizer hz _ h))
  constructor
  · intro he
    have h := congrFun (congrArg Subtype.val he) i
    change (x.val i).map (MulAut.conj (Pi.mulSingle (M := fun _ : I => S) i s i)) =
      x.val i at h
    exact hii.mp (by simpa using h)
  · intro h
    apply Subtype.ext
    funext j
    change (x.val j).map (MulAut.conj (Pi.mulSingle (M := fun _ : I => S) i s j)) = x.val j
    by_cases hj : j = i
    · subst j
      simpa using hii.mpr h
    · rw [Pi.mulSingle_eq_of_ne hj, map_one]
      exact Subgroup.map_id _

private theorem graphAction_centralizer :
    Subgroup.centralizer ((graphAction hz Γ).range : Set (Equiv.Perm (GraphPoints S Γ))) = ⊥ := by
  apply le_antisymm _ bot_le
  intro n hn
  apply Subgroup.mem_bot.mpr
  ext x
  apply Subtype.ext
  funext i
  ext s
  rw [← point_fixed_iff hz Γ, ← point_fixed_iff hz Γ]
  let p := graphAction hz Γ
    (embeddedInn (Fixing hz) (inn_le_fixing hz) (Pi.mulSingle i s))
  change p (n x) = n x ↔ p x = x
  have he := congrArg (fun e : Equiv.Perm (GraphPoints S Γ) => e x)
    (Subgroup.mem_centralizer_iff.mp hn p ⟨_, rfl⟩)
  change p (n x) = n (p x) at he
  rw [he, n.injective.eq_iff]

private def pointWith (P : Subgroup S) (hP : IsCoatom P)
    (T : Set I) (hT : graphSupport Γ T) : GraphPoints S Γ := by
  classical
  refine ⟨fun i => if i ∈ T then P else ⊤, fun i => ?_, ?_⟩
  · by_cases hi : i ∈ T <;> simp [hi, hP]
  · have he : supportOf (fun i => if i ∈ T then P else ⊤) = T := by
      ext i
      by_cases hi : i ∈ T <;> simp [supportOf, hi, hP.1]
    rwa [he]

omit [IsSimpleGroup S] [DecidableEq I] in
private theorem support_pointWith (P : Subgroup S) (hP : IsCoatom P)
    (T : Set I) (hT : graphSupport Γ T) :
    supportOf (pointWith Γ P hP T hT).val = T := by
  classical
  ext i
  change (if i ∈ T then P else ⊤) ≠ ⊤ ↔ i ∈ T
  by_cases hi : i ∈ T <;> simp [hi, hP.1]

private theorem singleAction_injective (P : Subgroup S) (hP : IsCoatom P) (i : I) :
    Injective (fun s : S => graphAction hz Γ
      (embeddedInn (Fixing hz) (inn_le_fixing hz) (Pi.mulSingle i s))) := by
  let g := (graphAction hz Γ).comp ((embeddedInn (Fixing hz) (inn_le_fixing hz)).comp
    (MonoidHom.mulSingle (fun _ : I => S) i))
  change Injective g
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker).resolve_right
  intro he
  have h : ∀ s : S, s ∈ P := by
    intro s
    let x := pointWith Γ P hP {i} (Or.inl ⟨i, rfl⟩)
    have hs : g s = 1 := show s ∈ g.ker by rw [he]; trivial
    have hfix := congrArg (fun e : Equiv.Perm (GraphPoints S Γ) => e x) hs
    have hs' := (point_fixed_iff hz Γ x i s).mp hfix
    simpa [x, pointWith] using hs'
  exact hP.1 ((Subgroup.eq_top_iff' P).mpr h)

variable [Finite I]

private theorem graphAction_injective (P : Subgroup S) (hP : IsCoatom P) :
    Injective (graphAction hz Γ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro h hh
  have he : graphAction hz Γ h = 1 := hh
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.pi_ext
  intro i s
  change h.val (Pi.mulSingle i s) = Pi.mulSingle i s
  rw [fixingSingle hz h]
  congr 1
  apply singleAction_injective hz Γ P hP i
  let f : (I → S) →* Fixing (I := I) hz := embeddedInn (Fixing hz) (inn_le_fixing hz)
  have hconj : f (h.val (Pi.mulSingle i s)) = h * f (Pi.mulSingle i s) * h⁻¹ :=
    Subtype.ext (conjugate_conj h.val _).symm
  change graphAction hz Γ (f (Pi.mulSingle i (h.val (Pi.mulSingle i s) i))) =
    graphAction hz Γ (f (Pi.mulSingle i s))
  rw [← fixingSingle hz h, hconj, map_mul, map_mul, map_inv, he, one_mul, inv_one, mul_one]

variable {P : Subgroup S} (hP : IsCoatom P)

private abbrev ActionImage := (graphAction hz Γ).range

private def actionEquiv : Fixing (I := I) hz ≃* ActionImage hz Γ :=
  MonoidHom.ofInjective (graphAction_injective hz Γ P hP)

private def inducedAut : norm (ActionImage hz Γ) →* MulAut (Fixing (I := I) hz) :=
  (MulAut.congr (actionEquiv hz Γ hP)).symm.toMonoidHom.comp
    (ActionImage hz Γ).normalizerMonoidHom

private def liftNormalizer : norm (ActionImage hz Γ) →* norm (Fixing (I := I) hz) :=
  (normalizerAut hz (Fixing hz) (inn_le_fixing hz)).symm.toMonoidHom.comp (inducedAut hz Γ hP)

private def liftAction : norm (ActionImage hz Γ) →* MulAut (I → S) :=
  (norm (Fixing (I := I) hz)).subtype.comp (liftNormalizer hz Γ hP)

private theorem inducedAut_apply (n : norm (ActionImage hz Γ)) (h : Fixing (I := I) hz) :
    graphAction hz Γ (inducedAut hz Γ hP n h) =
      n.val * graphAction hz Γ h * n.val⁻¹ := by
  exact congrArg Subtype.val ((actionEquiv hz Γ hP).apply_symm_apply
    ((ActionImage hz Γ).normalizerMonoidHom n (actionEquiv hz Γ hP h)))

private theorem liftAction_conjugate (n : norm (ActionImage hz Γ)) (x : I → S) :
    inducedAut hz Γ hP n (embeddedInn (Fixing hz) (inn_le_fixing hz) x) =
      embeddedInn (Fixing hz) (inn_le_fixing hz) (liftAction hz Γ hP n x) := by
  apply Subtype.ext
  have he := (normalizerAut hz (Fixing hz) (inn_le_fixing hz)).apply_symm_apply
    (inducedAut hz Γ hP n)
  rw [← he]
  exact conjugate_conj (liftAction hz Γ hP n) x

private theorem liftAction_eq (n : norm (ActionImage hz Γ)) (b : norm (Fixing (I := I) hz))
    (hb : ∀ h : Fixing (I := I) hz, graphAction hz Γ ((Fixing hz).normalizerMonoidHom b h) =
      n.val * graphAction hz Γ h * n.val⁻¹) :
    liftAction hz Γ hP n = b.val := by
  apply congrArg Subtype.val
  apply (normalizerAut hz (Fixing hz) (inn_le_fixing hz)).injective
  change (normalizerAut hz (Fixing hz) (inn_le_fixing hz))
    ((normalizerAut hz (Fixing hz) (inn_le_fixing hz)).symm (inducedAut hz Γ hP n)) =
    (Fixing hz).normalizerMonoidHom b
  rw [MulEquiv.apply_symm_apply]
  apply DFunLike.ext
  intro h
  exact graphAction_injective hz Γ P hP ((inducedAut_apply hz Γ hP n h).trans (hb h).symm)

omit [Finite I] in
private theorem imageNormalizer_injective :
    Injective (ActionImage hz Γ).normalizerMonoidHom := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker,
    graphAction_centralizer, Subgroup.bot_subgroupOf]

-- A normalizing permutation inducing the identity on the factors acts by an element of
-- Fixing. Its conjugation action determines it because the permutation centralizer is trivial.
private theorem coords_lift_eq_one (n : norm (ActionImage hz Γ)) :
    coords hz (liftAction hz Γ hP n) = 1 ↔ n.val ∈ ActionImage hz Γ := by
  constructor
  · intro hn
    let h : Fixing (I := I) hz := ⟨liftAction hz Γ hP n, hn⟩
    let m : norm (ActionImage hz Γ) := ⟨graphAction hz Γ h,
      (ActionImage hz Γ).le_normalizer ⟨h, rfl⟩⟩
    suffices n = m from this ▸ show m.val ∈ ActionImage hz Γ from ⟨h, rfl⟩
    apply imageNormalizer_injective hz Γ
    apply DFunLike.ext
    intro g
    obtain ⟨g, rfl⟩ := (actionEquiv hz Γ hP).surjective g
    apply Subtype.ext
    change n.val * graphAction hz Γ g * n.val⁻¹ =
      graphAction hz Γ h * graphAction hz Γ g * (graphAction hz Γ h)⁻¹
    have he := (normalizerAut hz (Fixing hz) (inn_le_fixing hz)).apply_symm_apply
      (inducedAut hz Γ hP n)
    rw [← inducedAut_apply hz Γ hP n g, ← he]
    change graphAction hz Γ (h * g * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨h, hh⟩
    let b : norm (Fixing (I := I) hz) := ⟨h.val, (Fixing hz).le_normalizer h.property⟩
    rw [liftAction_eq hz Γ hP n b]
    · exact h.property
    · intro g
      change graphAction hz Γ (h * g * h⁻¹) = _
      rw [map_mul, map_mul, map_inv, hh]

private def vertexPerm : norm (ActionImage hz Γ) →* Equiv.Perm I :=
  (coords hz).comp (liftAction hz Γ hP)

omit [Finite I] in
private theorem top_iff_fixed_factor (x : GraphPoints S Γ) (i : I) :
    x.val i = ⊤ ↔ ∀ u ∈ factor S i,
      graphAction hz Γ (embeddedInn (Fixing hz) (inn_le_fixing hz) u) x = x := by
  rw [Subgroup.eq_top_iff']
  constructor
  · rintro h _ ⟨s, rfl⟩
    exact (point_fixed_iff hz Γ x i s).mpr (h s)
  · intro h s
    exact (point_fixed_iff hz Γ x i s).mp (h (Pi.mulSingle i s) ⟨s, rfl⟩)

-- The induced automorphism transports the i-th factor to the image vertex's factor.
private theorem vertexPerm_top_iff (n : norm (ActionImage hz Γ)) (x : GraphPoints S Γ) (i : I) :
    (n.val x).val (vertexPerm hz Γ hP n i) = ⊤ ↔ x.val i = ⊤ := by
  rw [top_iff_fixed_factor hz Γ, top_iff_fixed_factor hz Γ]
  change (∀ u ∈ factor S (coordFun hz (liftAction hz Γ hP n) i), _) ↔ _
  rw [← map_factor_eq]
  simp only [Subgroup.mem_map]
  have hact (u : I → S) : graphAction hz Γ
      (embeddedInn (Fixing hz) (inn_le_fixing hz) (liftAction hz Γ hP n u)) (n.val x) =
      n.val (graphAction hz Γ (embeddedInn (Fixing hz) (inn_le_fixing hz) u) x) := by
    rw [← liftAction_conjugate hz Γ hP, inducedAut_apply hz Γ hP]
    change n.val (graphAction hz Γ (embeddedInn (Fixing hz) (inn_le_fixing hz) u)
      (n.val.symm (n.val x))) = _
    rw [Equiv.symm_apply_apply]
  constructor
  · intro h u hu
    apply n.val.injective
    rw [← hact]
    exact h _ ⟨u, hu, rfl⟩
  · rintro h u ⟨v, hv, rfl⟩
    exact (hact v).trans (congrArg n.val (h v hv))

private theorem support_vertexPerm (n : norm (ActionImage hz Γ)) (x : GraphPoints S Γ) :
    supportOf (n.val x).val = vertexPerm hz Γ hP n '' supportOf x.val := by
  ext j
  obtain ⟨i, rfl⟩ := (vertexPerm hz Γ hP n).surjective j
  exact (not_congr (vertexPerm_top_iff hz Γ hP n x i)).trans
    (((vertexPerm hz Γ hP n).injective.mem_set_image (s := supportOf x.val) (a := i)).symm)

omit [IsSimpleGroup S] [DecidableEq I] [Finite I] in
private theorem adj_of_pair_support (x : GraphPoints S Γ) {i j : I} (hij : i ≠ j)
    (h : supportOf x.val = {i, j}) : Γ.Adj i j := by
  have hi : i ∈ supportOf x.val := by rw [h]; simp
  have hj : j ∈ supportOf x.val := by rw [h]; simp
  rcases x.property.2 with ⟨k, hk⟩ | ⟨u, v, huv, he⟩
  · rw [hk, Set.mem_singleton_iff] at hi hj
    exact (hij (hi.trans hj.symm)).elim
  · rw [he, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · exact huv
    · exact huv.symm
    · exact (hij rfl).elim

private theorem vertexPerm_adj (n : norm (ActionImage hz Γ)) {i j : I} (h : Γ.Adj i j) :
    Γ.Adj (vertexPerm hz Γ hP n i) (vertexPerm hz Γ hP n j) := by
  let x := pointWith Γ P hP {i, j} (Or.inr ⟨i, j, h, rfl⟩)
  apply adj_of_pair_support Γ (n.val x) ((vertexPerm hz Γ hP n).injective.ne h.ne)
  rw [support_vertexPerm hz Γ hP]
  have hx : supportOf x.val = {i, j} := support_pointWith Γ P hP _ _
  rw [hx, Set.image_pair]

private def toGraphAut : norm (ActionImage hz Γ) →* (Γ ≃g Γ) where
  toFun n :=
    { toEquiv := vertexPerm hz Γ hP n
      map_rel_iff' := by
        intro i j
        refine ⟨fun h => ?_, vertexPerm_adj hz Γ hP n⟩
        have he := vertexPerm_adj hz Γ hP n⁻¹ h
        rw [map_inv] at he
        change Γ.Adj ((vertexPerm hz Γ hP n).symm (vertexPerm hz Γ hP n i))
          ((vertexPerm hz Γ hP n).symm (vertexPerm hz Γ hP n j)) at he
        simpa only [Equiv.symm_apply_apply] using he }
  map_one' := RelIso.ext fun i =>
    congrArg (fun e : Equiv.Perm I => e i) ((vertexPerm hz Γ hP).map_one)
  map_mul' n m := RelIso.ext
    (fun i => congrArg (fun e : Equiv.Perm I => e i) ((vertexPerm hz Γ hP).map_mul n m))

private theorem toGraphAut_ker :
    (toGraphAut hz Γ hP).ker = (ActionImage hz Γ).subgroupOf (norm (ActionImage hz Γ)) := by
  ext n
  change toGraphAut hz Γ hP n = 1 ↔ n.val ∈ ActionImage hz Γ
  refine Iff.trans ?_ (coords_lift_eq_one hz Γ hP n)
  change toGraphAut hz Γ hP n = 1 ↔ vertexPerm hz Γ hP n = 1
  exact ⟨congrArg RelIso.toEquiv, fun h => RelIso.ext fun i =>
    congrArg (fun e : Equiv.Perm I => e i) h⟩

omit [IsSimpleGroup S] [DecidableEq I] [Finite I] in
private theorem graphSupport_image (e : Γ ≃g Γ) {T : Set I} (hT : graphSupport Γ T) :
    graphSupport Γ (e '' T) := by
  rcases hT with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact Or.inl ⟨e i, Set.image_singleton⟩
  · exact Or.inr ⟨e i, e j, e.map_rel_iff.mpr hij, Set.image_pair _ _ _⟩

private def movePoint (e : Γ ≃g Γ) (x : GraphPoints S Γ) : GraphPoints S Γ := by
  refine ⟨fun i => x.val (e.symm i), fun i => x.property.1 _, ?_⟩
  have he : supportOf (fun i => x.val (e.symm i)) = e '' supportOf x.val := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change x.val (e.symm (e i)) ≠ ⊤ ↔ e i ∈ e '' supportOf x.val
    rw [RelIso.symm_apply_apply]
    exact (e.injective.mem_set_image (s := supportOf x.val) (a := i)).symm
  rw [he]
  exact graphSupport_image Γ e x.property.2

private def renamePoints (e : Γ ≃g Γ) : Equiv.Perm (GraphPoints S Γ) where
  toFun := movePoint Γ e
  invFun := movePoint Γ e.symm
  left_inv x := Subtype.ext (funext fun i => by
    change x.val (e.symm (e i)) = x.val i
    rw [RelIso.symm_apply_apply])
  right_inv x := Subtype.ext (funext fun i => by
    change x.val (e (e.symm i)) = x.val i
    rw [RelIso.apply_symm_apply])

omit [IsSimpleGroup S] [Finite I] in
private theorem reindex_single (e : Equiv.Perm I) (i : I) (s : S) :
    reindex e (Pi.mulSingle i s) = Pi.mulSingle (e i) s := by
  funext j
  change Pi.mulSingle (M := fun _ : I => S) i s (e.symm j) =
    Pi.mulSingle (M := fun _ : I => S) (e i) s j
  by_cases h : j = e i
  · subst j
    simp
  · have he : e.symm j ≠ i := fun he => h (by simp [← he])
    simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne he]

omit [Finite I] in
private theorem reindex_conj_action (e : Γ ≃g Γ) (b : norm (Fixing (I := I) hz))
    (hb : b.val = reindex e.toEquiv) (h : Fixing (I := I) hz) :
    graphAction hz Γ ((Fixing hz).normalizerMonoidHom b h) =
      renamePoints Γ e * graphAction hz Γ h * (renamePoints Γ e)⁻¹ := by
  have hlocal (i : I) : localAut hz i ((Fixing hz).normalizerMonoidHom b h) =
      localAut hz (e.symm i) h := by
    apply DFunLike.ext
    intro s
    simp only [localAut_apply]
    change (b.val (h.val (b.val.symm (Pi.mulSingle i s)))) i =
      h.val (Pi.mulSingle (e.symm i) s) (e.symm i)
    rw [hb]
    change h.val (reindex (S := S) e.toEquiv.symm (Pi.mulSingle i s)) (e.symm i) = _
    rw [reindex_single]
    rfl
  ext x
  apply Subtype.ext
  funext i
  change (localAut hz i ((Fixing hz).normalizerMonoidHom b h)).mapSubgroup (x.val i) =
    (localAut hz (e.symm i) h).mapSubgroup (x.val (e (e.symm i)))
  rw [hlocal, RelIso.apply_symm_apply]

private theorem toGraphAut_surjective : Surjective (toGraphAut hz Γ hP) := by
  intro e
  have hnormal : (Fixing (I := I) hz).Normal :=
    inferInstanceAs ((coords (I := I) hz).ker.Normal)
  let b : norm (Fixing (I := I) hz) := ⟨reindex e.toEquiv, by
    rw [show norm (Fixing (I := I) hz) = ⊤ from
      Subgroup.normalizer_eq_top_iff.mpr hnormal]
    trivial⟩
  let n := renamePoints (S := S) Γ e
  have hb : ∀ h : Fixing (I := I) hz,
      graphAction hz Γ ((Fixing hz).normalizerMonoidHom b h) =
        n * graphAction hz Γ h * n⁻¹ :=
    reindex_conj_action hz Γ e b rfl
  have hn : n ∈ norm (ActionImage hz Γ) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨_, hb h⟩
    · rintro ⟨g, hg⟩
      obtain ⟨h, rfl⟩ := ((Fixing hz).normalizerMonoidHom b).surjective g
      have he := (hb h).symm.trans hg
      exact ⟨h, mul_left_cancel (mul_right_cancel he)⟩
  refine ⟨⟨n, hn⟩, RelIso.ext fun i => ?_⟩
  change vertexPerm hz Γ hP ⟨n, hn⟩ i = e i
  change coords hz (liftAction hz Γ hP ⟨n, hn⟩) i = e i
  rw [liftAction_eq hz Γ hP ⟨n, hn⟩ b hb]
  change coords hz (reindex e.toEquiv) i = e i
  exact congrArg (fun p : Equiv.Perm I => p i) (coords_reindex hz e.toEquiv)

end Graph

private theorem realize_graph [Finite I] [Finite S] (hz : Subgroup.center S = ⊥)
    (Γ : SimpleGraph I) (P : Subgroup S) (hP : IsCoatom P) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (φ : MulAut G →* (Γ ≃g Γ)),
      Surjective φ ∧ φ.ker = (MulAut.conj : G →* MulAut G).range := by
  classical
  exact outer_realize hz (coords hz) (fun e => ⟨reindex e, coords_reindex hz e⟩)
    (coords_conj hz) (ActionImage hz Γ) (toGraphAut hz Γ hP)
    (toGraphAut_surjective hz Γ hP) (toGraphAut_ker hz Γ hP)


section Realization

local notation "A₅" => alternatingGroup (Fin 5)

private theorem realize_finite_group (K : Type) [Group K] [Finite K] :
    ∃ (G : Type) (_ : Group G) (_ : Finite G)
      (φ : MulAut G →* K), Surjective φ ∧ φ.ker = (MulAut.conj : G →* MulAut G).range := by
  classical
  let _ := Fintype.ofFinite K
  obtain ⟨n, Γ, ⟨e⟩⟩ := MathlibExt.Combinatorics.SimpleGraph.FruchtWanted.frucht (G := K)
  have hS : IsSimpleGroup A₅ := alternatingGroup.isSimpleGroup (by simp)
  have hz : Subgroup.center A₅ = ⊥ := alternatingGroup.center_eq_bot (by simp)
  have hfinite : Finite (Subgroup A₅) :=
    Finite.of_injective (fun P : Subgroup A₅ => (P : Set A₅)) SetLike.coe_injective
  obtain ⟨P, hP, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup A₅)).resolve_left bot_ne_top
  obtain ⟨G, _, _, q, hq, hk⟩ := realize_graph hz Γ P hP
  refine ⟨G, inferInstance, inferInstance, e.symm.toMonoidHom.comp q,
    e.symm.surjective.comp hq, ?_⟩
  rw [← hk]
  ext a
  change e.symm (q a) = 1 ↔ q a = 1
  rw [← e.symm.map_one, e.symm.injective.eq_iff]

end Realization
/--
**Every finite group is the outer automorphism group of a finite group.** For every finite group
$K$ there are a finite group $G$ and a surjective homomorphism $\mathrm{Aut}(G) \to K$ whose
kernel is the group $\mathrm{Inn}(G)$ of inner automorphisms of $G$; equivalently,
$\mathrm{Out}(G) = \mathrm{Aut}(G) / \mathrm{Inn}(G)$ is isomorphic to $K$. That is, the answer
to Kourovka Problem 16.59 is positive.

The Kourovka Archive records the answer "Yes, it does", citing Cornulier's MathOverflow answer.

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.59 (D. MacHale);
resolution: Y. Cornulier, answer to MathOverflow question 372480 (Is every finite group the outer
automorphism group of a finite group?), 2020, Kourovka Archive, Problem 16.59 (Yes, it does),
https://mathoverflow.net/questions/372480/is-every-finite-group-the-outer-automorphism-group-of-a-finite-group/372563.
-/
public theorem everyFiniteGroupIsOuterAutomorphismGroup_holds :
    everyFiniteGroupIsOuterAutomorphismGroup :=
  realize_finite_group

end

end MathlibExt.GroupTheory.OuterAutomorphismGroupRealizationKourovka16Problem59Wanted
