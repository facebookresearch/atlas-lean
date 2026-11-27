/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Frattini
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Goursat
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import MathlibExt.GroupTheory.BurnsidePaqb

/-!
# Radical hereditary formations need not be composition formations (Kourovka Notebook Problem 12.7)

Kourovka Notebook, Archive of Solved Problems, Problem 12.7 (A. F. Vasil'ev): is every radical
hereditary formation of finite groups a composition formation?

The counterexample uses groups whose soluble residual is a direct power of `PSL(2, ZMod 5)`.
The central product of `SL(2, ZMod 5)` with a cyclic group of order four witnesses the failure
of soluble saturation.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.7 (A. F.
Vasil'ev). UnsolvedMath record UM-00700827 (`KOU-12.7`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A formation contains the trivial group and is closed under quotients and
subdirect products; a radical class is a Fitting class (closed under normal subgroups and under
products of two normal members); hereditary means closed under all subgroups. A composition
formation (Shemetkov) is taken in its standard equivalent form, a solubly saturated (Baer-local)
formation: `G ⧸ Φ(R(G)) ∈ 𝔉` implies `G ∈ 𝔉`, with `R(G)` the soluble radical. The three names are
synonyms in E. N. Myslovets and A. F. Vasil'ev (arXiv:1603.04018, Section 2), whose definition
allows any soluble normal subgroup `N` in place of `R(G)`; this is equivalent for formations, since
`Φ(N) ≤ Φ(R(G))`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted

/-- **Isomorphism-closed class of groups.** A class of groups $X$ is a property of groups that is
invariant under isomorphism: if a group $H$ belongs to $X$ and $K$ is a group isomorphic to $H$,
then $K$ belongs to $X$.

Infinite groups may belong to a class; apart from isomorphism invariance, the conditions imposed
on classes below concern only finite groups. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Quotient lying in a class.** For a class of groups $X$, a group $G$ and a subgroup $N$ of $G$,
this holds when $N$ is normal in $G$ and the quotient group $G/N$ belongs to $X$. -/
def QuotMem (X : GroupClass) {G : Type} [Group G] (N : Subgroup G) : Prop :=
  ∃ _ : N.Normal, X.mem (G ⧸ N)

/-- **Formation of finite groups.** A class of groups $X$ is a formation if it contains the trivial
group, for every finite group $G$ in $X$ and every normal subgroup $N$ of $G$ the quotient $G/N$
belongs to $X$, and for every finite group $G$ with normal subgroups $N_1, N_2$ such that
$G/N_1$ and $G/N_2$ belong to $X$, the quotient $G/(N_1 \cap N_2)$ belongs to $X$. -/
def IsFormation (X : GroupClass) : Prop :=
  X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- **Radical (Fitting) class.** A class of groups $X$ is radical if, for every finite group $G$,
every normal subgroup of $G$ belongs to $X$ whenever $G$ does, and whenever $N_1, N_2$ are normal
subgroups of $G$ that belong to $X$, their product $N_1 N_2$ belongs to $X$. -/
def IsRadical (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- **Hereditary class of groups.** A class of groups $X$ is hereditary if every subgroup of a
finite group in $X$ belongs to $X$. -/
def IsHereditary (X : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), X.mem G → X.mem H

/-- **Soluble radical.** A subgroup $R$ of a group $G$ is the soluble radical of $G$ if $R$ is a
soluble normal subgroup of $G$ that contains every soluble normal subgroup of $G$. -/
def IsSolubleRadical {G : Type} [Group G] (R : Subgroup G) : Prop :=
  R.Normal ∧ Group.IsSolvable R ∧ ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N ≤ R

/-- **Solubly saturated class.** A class of groups $X$ is solubly saturated (a composition class)
if, for every finite group $G$ with soluble radical $R$, whenever the Frattini subgroup $\Phi(R)$
of $R$ is normal in $G$ and $G/\Phi(R)$ belongs to $X$, the group $G$ belongs to $X$.

A formation with this property is a composition (solubly saturated, Baer-local) formation. -/
def IsComposition (X : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R : Subgroup G), IsSolubleRadical R →
    QuotMem X ((frattini R).map R.subtype) → X.mem G

/-- **Kourovka Problem 12.7 (Vasil'ev).** The statement that every radical hereditary formation of
finite groups is a composition formation: every class of groups that is a formation, a radical
class and a hereditary class is solubly saturated. -/
def radicalHereditaryFormationIsComposition : Prop :=
  ∀ X : GroupClass, IsFormation X → IsRadical X → IsHereditary X → IsComposition X

open Subgroup Function Group

variable {S G H : Type} [Group S] [Group G] [Group H]

/-- `D` is generated by images of `S` that are normal in `D`. -/
private def Generated (S : Type) [Group S] (D : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (∀ f : S →* G, f.range ≤ D → D ≤ normalizer f.range → f.range ≤ L) → D ≤ L

private theorem generated_bot : Generated S (⊥ : Subgroup G) := fun _ _ => bot_le

private theorem generated_map {D : Subgroup G} (hD : Generated S D) (g : G →* H) :
    Generated S (D.map g) := by
  intro L hL
  apply map_le_iff_le_comap.mpr (hD _ ?_)
  intro f hf hn
  apply map_le_iff_le_comap.mp
  rw [← MonoidHom.range_comp]
  apply hL
  · rw [MonoidHom.range_comp]
    exact map_mono hf
  · rw [MonoidHom.range_comp]
    exact (map_mono hn).trans (le_normalizer_map _)

private theorem generated_of_map {D : Subgroup G} (g : G →* H) (hg : Injective g)
    (hD : Generated S (D.map g)) : Generated S D := by
  intro L hL
  apply (map_le_map_iff_of_injective hg).mp (hD (L.map g) ?_)
  intro f hf hn
  have hfr : f.range ≤ g.range := hf.trans (map_le_range ..)
  let t := (MonoidHom.ofInjective hg).symm.toMonoidHom.comp
    (f.codRestrict g.range (fun x => hfr ⟨x, rfl⟩))
  have ht : g.comp t = f := by
    ext x
    exact MonoidHom.apply_ofInjective_symm hg _
  rw [← ht, MonoidHom.range_comp] at hf hn ⊢
  apply map_mono (hL t ((map_le_map_iff_of_injective hg).mp hf) ?_)
  rw [le_normalizer_iff_commutator_le_right]
  apply (map_le_map_iff_of_injective hg).mp
  rw [map_commutator]
  exact le_normalizer_iff_commutator_le_right.mp hn

private theorem range_inf_or_le [IsSimpleGroup S] (f : S →* G) (N : Subgroup G) [N.Normal] :
    f.range ⊓ N = ⊥ ∨ f.range ≤ N := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap f) with h | h
  · left
    rw [← map_comap_eq, h, Subgroup.map_bot]
  · right
    rw [MonoidHom.range_eq_map, map_le_iff_le_comap, h]

/-- A simple factor normal in a normal subgroup either lies in `N` or centralizes `N`. -/
private theorem component_or_centralizes [IsSimpleGroup S] [IsPerfect S]
    {D : Subgroup G} [D.Normal] (f : S →* G) (hf : f.range ≤ D)
    (hn : D ≤ normalizer f.range) (N : Subgroup G) [N.Normal] :
    f.range ≤ N ∨ f.range ≤ centralizer N := by
  rcases range_inf_or_le f N with hi | h
  · right
    have hcomm : ⁅N ⊓ D, f.range⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← hi]
      refine le_inf (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hn)) ?_
      exact (commutator_mono inf_le_left le_rfl).trans (commutator_le_left N _)
    have hND : ⁅N, f.range⁆ ≤ N ⊓ D :=
      le_inf (commutator_le_left ..) ((commutator_mono le_rfl hf).trans (commutator_le_right ..))
    -- The three subgroups lemma and perfectness turn the double commutator into the claim.
    have htr : ⁅⁅N, f.range⁆, f.range⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_mono hND le_rfl).trans hcomm.le)
    have := IsPerfect.range f
    rw [← commutator_eq_bot_iff_le_centralizer, ← f.range.commutator_eq_self]
    exact commutator_commutator_eq_bot_of_rotate (by rwa [commutator_comm f.range N]) htr
  · exact Or.inl h

private theorem generated_sup [IsSimpleGroup S] [IsPerfect S] {D E : Subgroup G}
    [D.Normal] [E.Normal] (hD : Generated S D) (hE : Generated S E) : Generated S (D ⊔ E) := by
  intro L hL
  have side (A B : Subgroup G) [A.Normal] [B.Normal] (ha : Generated S A) (hb : Generated S B)
      (he : A ⊔ B = D ⊔ E) : A ≤ L := by
    apply ha
    intro f hf hn
    apply hL f (he ▸ hf.trans le_sup_left)
    rw [← he]
    refine sup_le hn (hb _ ?_)
    intro g hg hgn
    rcases component_or_centralizes g hg hgn A with h | h
    · exact h.trans hn
    · exact (h.trans (centralizer_le hf)).trans (centralizer_le_normalizer _)
  exact sup_le (side D E hD hE rfl) (side E D hE hD (sup_comm ..))

private theorem generated_self : Generated S (⊤ : Subgroup S) := by
  intro L h
  have hi : (MonoidHom.id S).range = ⊤ := MonoidHom.range_eq_top.mpr surjective_id
  exact hi ▸ h (MonoidHom.id S) le_top (hi ▸ le_normalizer)

private theorem generated_perfect [IsPerfect S] {D : Subgroup G} (hd : Generated S D) :
    IsPerfect D := by
  apply Subgroup.isPerfect_iff.mpr (le_antisymm D.commutator_le_self (hd _ ?_))
  intro f hf _
  have := IsPerfect.range f
  exact f.range.commutator_eq_self.ge.trans (commutator_mono hf hf)

/-- A nontrivial normal simple factor splits off with its centralizer as complement. -/
private theorem split_factor [IsSimpleGroup S] [IsPerfect S] [Finite G] [Nontrivial G]
    (hD : Generated S (⊤ : Subgroup G)) :
    ∃ C : Subgroup G, Nat.card C < Nat.card G ∧ Nonempty (G ≃* S × C) := by
  obtain ⟨f, hn, hne⟩ : ∃ f : S →* G, (⊤ : Subgroup G) ≤ normalizer f.range ∧ f.range ≠ ⊥ := by
    by_contra! h
    exact top_ne_bot (le_bot_iff.mp (hD ⊥ (fun f _ hn => (h f hn).le)))
  have := normalizer_eq_top_iff.mp (top_le_iff.mp hn)
  let C := centralizer (f.range : Set G)
  have hnot : ¬ f.range ≤ C := by
    intro h
    have := le_centralizer_iff_isMulCommutative.mp h
    have := IsPerfect.range f
    have := IsPerfect.subsingleton_of_isMulCommutative (G := f.range)
    exact hne (eq_bot_of_subsingleton _)
  have hi := (range_inf_or_le f C).resolve_right hnot
  have htop : f.range ⊔ C = ⊤ := by
    apply top_le_iff.mp (hD _ ?_)
    intro g _ hg
    rcases range_inf_or_le g f.range with hd | h
    · have := normalizer_eq_top_iff.mp (top_le_iff.mp hg)
      exact (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
        ((commutator_le_inf g.range f.range).trans hd.le))).trans le_sup_right
    · exact h.trans le_sup_left
  have inj : Injective f := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).mp h
    · exact False.elim (hne (MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp h)))
  let F := f.noncommCoprod C.subtype (fun x y => y.property _ ⟨x, rfl⟩)
  have hF : Bijective F := by
    constructor
    · apply (MonoidHom.noncommCoprod_injective ..).mpr
      exact ⟨inj, C.subtype_injective, by simpa [disjoint_iff] using hi.le⟩
    · apply MonoidHom.range_eq_top.mp
      rw [show F.range = f.range ⊔ C.subtype.range from MonoidHom.noncommCoprod_range ..,
        range_subtype]
      exact htop
  refine ⟨C, ?_, ⟨(MulEquiv.ofBijective F hF).symm⟩⟩
  simpa using (card_lt_of_lt (lt_top_iff_ne_top.mpr (show C ≠ ⊤ from fun h =>
    hnot (h ▸ le_top))))

private theorem generated_prod {P : Subgroup G} {Q : Subgroup H} (hp : Generated S P)
    (hq : Generated S Q) : Generated S (P.prod Q) := by
  intro L hL
  rw [prod_le_iff]
  constructor
  · apply map_le_iff_le_comap.mpr (hp _ ?_)
    intro f hf hn
    apply map_le_iff_le_comap.mp
    rw [← MonoidHom.range_comp]
    apply hL
    · rintro _ ⟨x, rfl⟩
      exact ⟨hf ⟨_, rfl⟩, Q.one_mem⟩
    · rw [MonoidHom.range_comp, le_normalizer_iff]
      rintro ⟨x, y⟩ ⟨hx, _⟩
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨x * a * x⁻¹, (le_normalizer_iff.mp hn) _ hx _ ha, by simp⟩
  · apply map_le_iff_le_comap.mpr (hq _ ?_)
    intro f hf hn
    apply map_le_iff_le_comap.mp
    rw [← MonoidHom.range_comp]
    apply hL
    · rintro _ ⟨x, rfl⟩
      exact ⟨P.one_mem, hf ⟨_, rfl⟩⟩
    · rw [MonoidHom.range_comp, le_normalizer_iff]
      rintro ⟨x, y⟩ ⟨_, hy⟩
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨y * a * y⁻¹, (le_normalizer_iff.mp hn) _ hy _ ha, by simp⟩

private theorem generated_of_perfect_prod [IsSimpleGroup S]
    (minimal : ∀ J : Subgroup S, J ≠ ⊤ → Group.IsSolvable J)
    (P : Subgroup (S × G)) [IsPerfect P] (hQ : Generated S (P.map (MonoidHom.snd ..))) :
    Generated S P := by
  let u := (MonoidHom.fst S G).domRestrict P
  -- The intersection with the first factor is either trivial or the whole simple group.
  by_cases h : P.goursatFst = ⊥
  · let v := (MonoidHom.snd S G).domRestrict P
    have hv : Injective v := by
      rw [injective_iff_map_eq_one]
      rintro ⟨⟨x, y⟩, hxy⟩ (hy : y = 1)
      subst y
      have hx := mem_goursatFst.mpr hxy
      rw [h] at hx
      exact Subtype.ext (Prod.ext (mem_bot.mp hx) rfl)
    have ht : Generated S (⊤ : Subgroup P) := generated_of_map v hv (by
      simpa only [Subgroup.map_top, v, MonoidHom.domRestrict_range] using hQ)
    simpa only [Subgroup.map_top, range_subtype] using generated_map ht P.subtype
  · have hu : Surjective u := by
      by_contra hsurj
      have := minimal u.range (fun hh => hsurj (MonoidHom.range_eq_top.mp hh))
      have := IsPerfect.range u
      have hs : Subsingleton u.range := by
        by_contra! hnt
        exact IsPerfect.not_isSolvable (G := u.range) inferInstance
      apply h (le_bot_iff.mp ?_)
      intro x hx
      exact (eq_bot_of_subsingleton u.range ▸ show u (⟨(x, 1), mem_goursatFst.mp hx⟩ : P) ∈
        u.range from ⟨_, rfl⟩)
    have := normal_goursatFst (I := P) hu
    have ht := (IsSimpleGroup.eq_bot_or_eq_top_of_normal P.goursatFst).resolve_left h
    have hl (x : S) : (x, (1 : G)) ∈ P := mem_goursatFst.mp (ht ▸ mem_top _)
    have he : P = (⊤ : Subgroup S).prod (P.map (MonoidHom.snd ..)) := by
      apply le_antisymm
      · intro a ha
        exact ⟨mem_top _, a, ha, rfl⟩
      · rintro ⟨x, y⟩ ⟨_, ⟨⟨z, w⟩, hzw, rfl⟩⟩
        simpa using P.mul_mem (hl (x * z⁻¹)) hzw
    rw [he]
    exact generated_prod generated_self hQ

private theorem generated_subgroup [IsSimpleGroup S] [IsPerfect S]
    (minimal : ∀ J : Subgroup S, J ≠ ⊤ → Group.IsSolvable J) {G : Type} [Group G] [Finite G]
    (hG : Generated S (⊤ : Subgroup G)) (P : Subgroup G) [IsPerfect P] : Generated S P := by
  cases subsingleton_or_nontrivial G with
  | inl h => simpa [eq_bot_of_subsingleton P] using (generated_bot (S := S) (G := G))
  | inr h =>
    obtain ⟨C, hC, ⟨e⟩⟩ := split_factor hG
    let v := (MonoidHom.snd S C).comp e.toMonoidHom
    have hv : Surjective v := Prod.snd_surjective.comp e.surjective
    have hc : Generated S (⊤ : Subgroup C) :=
      map_top_of_surjective v hv ▸ generated_map hG v
    have := IsPerfect.map (H := P) e.toMonoidHom
    have := IsPerfect.map (H := P.map e.toMonoidHom) (MonoidHom.snd S C)
    apply generated_of_map e.toMonoidHom e.injective
    apply generated_of_perfect_prod minimal
    exact generated_subgroup (G := C) minimal hc _
termination_by Nat.card G

private theorem generated_subgroup_of_le [IsSimpleGroup S] [IsPerfect S] [Finite G]
    (minimal : ∀ J : Subgroup S, J ≠ ⊤ → Group.IsSolvable J) {P D : Subgroup G}
    (h : P ≤ D) [IsPerfect P] (hd : Generated S D) : Generated S P := by
  have ht : Generated S (⊤ : Subgroup D) := generated_of_map D.subtype D.subtype_injective
    (by simpa only [Subgroup.map_top, range_subtype] using hd)
  let e := subgroupOfEquivOfLe h
  have := IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  simpa only [map_subgroupOf_eq_of_le h] using
    generated_map (generated_subgroup minimal ht (P.subgroupOf D)) D.subtype

private theorem stable_after [Finite G] (k : ℕ) :
    ∃ n ≥ k, IsPerfect (Subgroup.derivedSeries G n) := by
  classical
  let c (i : ℕ) := Nat.card (Subgroup.derivedSeries G (k + i))
  have hex : ∃ m, ∃ i, c i = m := ⟨_, 0, rfl⟩
  let m := Nat.find hex
  obtain ⟨i, hi⟩ : ∃ i, c i = m := Nat.find_spec hex
  refine ⟨k + i, Nat.le_add_right _ _, Subgroup.isPerfect_iff.mpr ?_⟩
  apply (Subgroup.derivedSeries_antitone G (Nat.le_succ (k + i))).eq_of_not_lt
  intro hlt
  have hl : c (i + 1) < c i := card_lt_of_lt hlt
  exact hl.not_ge (hi ▸ Nat.find_min' hex (show ∃ j, c j = c (i + 1) from ⟨_, rfl⟩))

/-- For finite groups and nonabelian simple `S`, the soluble residual is a direct power of `S`. -/
private def residualClass (S : Type) [Group S] : GroupClass where
  mem G _ := ∃ n, Generated S (Subgroup.derivedSeries G n)
  iso G H _ _ e := by
    rintro ⟨n, hn⟩
    exact ⟨n, Subgroup.map_derivedSeries_eq (f := e.toMonoidHom) e.surjective n ▸
      generated_map hn e.toMonoidHom⟩

private theorem class_hereditary [IsSimpleGroup S] [IsPerfect S]
    (minimal : ∀ J : Subgroup S, J ≠ ⊤ → Group.IsSolvable J) : IsHereditary (residualClass S) := by
  rintro G _ _ H ⟨n, hn⟩
  obtain ⟨m, hmn, hm⟩ := stable_after (G := H) n
  have := IsPerfect.map (H := Subgroup.derivedSeries H m) H.subtype
  refine ⟨m, generated_of_map H.subtype H.subtype_injective ?_⟩
  apply generated_subgroup_of_le minimal (hd := hn)
  exact (Subgroup.map_derivedSeries_le_derivedSeries _ _).trans
    (Subgroup.derivedSeries_antitone G hmn)

private theorem class_map (f : G →* H) (hf : Surjective f) :
    (residualClass S).mem G → (residualClass S).mem H := by
  rintro ⟨n, hn⟩
  exact ⟨n, Subgroup.map_derivedSeries_eq hf n ▸ generated_map hn f⟩

private theorem class_of_soluble [Group.IsSolvable G] : (residualClass S).mem G := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact ⟨n, hn ▸ generated_bot⟩

private theorem perfect_le_derived (P : Subgroup G) [IsPerfect P] (n : ℕ) :
    P ≤ Subgroup.derivedSeries G n := by
  have h := Subgroup.map_derivedSeries_le_derivedSeries P.subtype n
  simpa only [IsPerfect.derivedSeries_eq_top, Subgroup.map_top, range_subtype] using h

private theorem class_of_quotient [IsPerfect S] (D : Subgroup G) [D.Normal]
    (hd : Generated S D) [Group.IsSolvable (G ⧸ D)] : (residualClass S).mem G := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G ⧸ D)
  have he := (Subgroup.map_derivedSeries_eq (QuotientGroup.mk'_surjective D) n).trans hn
  have := generated_perfect hd
  have hle : Subgroup.derivedSeries G n ≤ D := by
    simpa using (Subgroup.derivedSeries G n).map_eq_bot_iff.mp he
  exact ⟨n, le_antisymm hle (perfect_le_derived D n) ▸ hd⟩

private theorem soluble_image {n : ℕ} (f : G →* H) (h : Subgroup.derivedSeries G n ≤ f.ker) :
    Group.IsSolvable f.range := by
  refine ⟨n, ?_⟩
  rw [← Subgroup.map_derivedSeries_eq f.rangeRestrict_surjective, Subgroup.map_eq_bot_iff]
  exact fun x hx => Subtype.ext (h hx)

private theorem soluble_join (A B : Subgroup G) [A.Normal] [Group.IsSolvable A]
    [Group.IsSolvable B] (ht : A ⊔ B = ⊤) : Group.IsSolvable G := by
  let q := QuotientGroup.mk' A
  have hq : Surjective (q.domRestrict B) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.domRestrict_range, ← map_top_of_surjective q (QuotientGroup.mk'_surjective A),
      ← ht, Subgroup.map_sup, A.map_eq_bot_iff.mpr (by simp [q]), bot_sup_eq]
  have := Group.isSolvable_of_surjective hq
  exact Group.isSolvable_of_subgroup_quotient A

private theorem class_join [IsSimpleGroup S] [IsPerfect S] (A B : Subgroup G)
    [A.Normal] [B.Normal] (ht : A ⊔ B = ⊤) :
    (residualClass S).mem A → (residualClass S).mem B → (residualClass S).mem G := by
  rintro ⟨n, hn⟩ ⟨m, hm⟩
  let D := (Subgroup.derivedSeries A n).map A.subtype
  let E := (Subgroup.derivedSeries B m).map B.subtype
  -- Modulo the two perfect residuals, the two normal factors have soluble images.
  let q := QuotientGroup.mk' (D ⊔ E)
  have sol (K : Subgroup G) (j : ℕ) (h : (Subgroup.derivedSeries K j).map K.subtype ≤ D ⊔ E) :
      Group.IsSolvable (K.map q) := by
    rw [← MonoidHom.domRestrict_range]
    apply soluble_image (q.domRestrict K) (n := j)
    apply (map_le_iff_le_comap.mp h).trans
    intro k hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have := sol A n le_sup_left
  have := sol B m le_sup_right
  have := soluble_join (A.map q) (B.map q) (by
    rw [← Subgroup.map_sup, ht, map_top_of_surjective q (QuotientGroup.mk'_surjective _)])
  exact class_of_quotient (D ⊔ E)
    (generated_sup (generated_map hn A.subtype) (generated_map hm B.subtype))

private theorem class_radical [IsSimpleGroup S] [IsPerfect S]
    (minimal : ∀ J : Subgroup S, J ≠ ⊤ → Group.IsSolvable J) : IsRadical (residualClass S) := by
  refine ⟨fun G _ _ N _ => class_hereditary minimal G N, ?_⟩
  intro G _ _ A B hA hB ha hb
  let T := A ⊔ B
  apply class_join (A.subgroupOf T) (B.subgroupOf T)
    (codisjoint_iff.mp (codisjoint_subgroupOf_sup A B))
  · exact (residualClass S).iso _ _ (subgroupOfEquivOfLe le_sup_left).symm ha
  · exact (residualClass S).iso _ _ (subgroupOfEquivOfLe le_sup_right).symm hb

private theorem class_prod [IsSimpleGroup S] [IsPerfect S] {A B : Type} [Group A] [Group B]
    (ha : (residualClass S).mem A) (hb : (residualClass S).mem B) :
    (residualClass S).mem (A × B) := by
  let t := MonoidHom.inl A B
  let u := MonoidHom.inr A B
  have : t.range.Normal := by
    have he : t.range = (MonoidHom.snd A B).ker := by ext ⟨a, b⟩; simp [t, mem_prod, eq_comm]
    rw [he]
    infer_instance
  have : u.range.Normal := by
    have he : u.range = (MonoidHom.fst A B).ker := by ext ⟨a, b⟩; simp [u, mem_prod, eq_comm]
    rw [he]
    infer_instance
  apply class_join t.range u.range _ (class_map _ t.rangeRestrict_surjective ha)
    (class_map _ u.rangeRestrict_surjective hb)
  apply top_le_iff.mp
  intro x _
  exact Prod.fst_mul_snd x ▸ mul_mem_sup (show t x.1 ∈ t.range from ⟨_, rfl⟩)
    (show u x.2 ∈ u.range from ⟨_, rfl⟩)

private theorem class_formation [IsSimpleGroup S] [IsPerfect S]
    (minimal : ∀ J : Subgroup S, J ≠ ⊤ → Group.IsSolvable J) : IsFormation (residualClass S) := by
  refine ⟨class_of_soluble, fun G _ _ N _ => class_map _ (QuotientGroup.mk'_surjective N), ?_⟩
  intro G _ _ N M _ _ hN hM
  let f := (QuotientGroup.mk' N).prod (QuotientGroup.mk' M)
  have e := (QuotientGroup.quotientKerEquivRange f).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (show f.ker = N ⊓ M by simp [f, MonoidHom.ker_prod]))
  exact (residualClass S).iso _ _ e (class_hereditary minimal _ f.range (class_prod hN hM))

open scoped MatrixGroups

private theorem primeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] primeFive

private abbrev SL₂ := SL(2, ZMod 5)
private abbrev PSL₂ := PSL(2, ZMod 5)
private abbrev C₄ := Multiplicative (ZMod 4)

private theorem cover_card : Nat.card SL₂ = 120 := by
  rw [SL₂, Matrix.card_SL_field (𝔽 := ZMod 5) 2]
  norm_num [Fin.prod_univ_two, ZMod.card]

private theorem center_card : Nat.card (center SL₂) = 2 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := ZMod 5)
    (0 : Fin 2)).toEquiv]
  simpa using (IsPrimitiveRoot.neg_one 5 (by decide) (R := ZMod 5)).card_rootsOfUnity

private theorem simple_card : Nat.card PSL₂ = 60 := by
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div, cover_card, center_card]

private theorem cover_perfect : IsPerfect SL₂ := by
  unfold SL₂
  exact ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 5)) (by decide) (by decide)⟩

private theorem simple_simple : IsSimpleGroup PSL₂ := by
  unfold PSL₂
  exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod 5) (by norm_num)

attribute [local instance] cover_perfect simple_simple

private theorem simple_perfect : IsPerfect PSL₂ :=
  inferInstanceAs (IsPerfect (SL₂ ⧸ center SL₂))

attribute [local instance] simple_perfect

private theorem minimal_simple (J : Subgroup PSL₂) (hJ : J ≠ ⊤) : Group.IsSolvable J := by
  have hd := J.card_subgroup_dvd_card
  rw [simple_card] at hd
  have hlt : Nat.card J < 60 := by
    simpa only [card_top, simple_card] using card_lt_of_lt (lt_top_iff_ne_top.mpr hJ)
  have h30 : Nat.card J ≠ 30 := by
    intro h
    have hn := J.normal_of_index_eq_two (by rw [J.index_eq_card_div, simple_card, h])
    have hb := (IsSimpleGroup.eq_bot_or_eq_top_of_normal J).resolve_right hJ
    simp [hb] at h
  -- Each remaining divisor of 60 involves at most two primes.
  have arith : ∀ n : Fin 60, n.val ∣ 60 → n.val ≠ 30 →
      ∃ p q : Fin 6, ∃ a b : Fin 3,
        p.val.Prime ∧ q.val.Prime ∧ n.val = p.val ^ a.val * q.val ^ b.val := by decide
  obtain ⟨p, q, a, b, hp, hq, hn⟩ := arith ⟨_, hlt⟩ hd h30
  let _ := Fintype.ofFinite J
  exact BurnsidePaqb.burnside_paqb _ _ _ _ hp hq (by simpa [Nat.card_eq_fintype_card] using hn)

private theorem cover_outside : ¬ (residualClass PSL₂).mem SL₂ := by
  have : Nontrivial SL₂ := Finite.one_lt_card_iff_nontrivial.mp (by rw [cover_card]; decide)
  rintro ⟨n, hn⟩
  rw [IsPerfect.derivedSeries_eq_top] at hn
  obtain ⟨C, _, ⟨e⟩⟩ := split_factor hn
  have h := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, simple_card, cover_card] at h
  have hc : Nat.card C = 2 := by omega
  have := (isCyclic_of_prime_card hc).isMulCommutative
  let t := (MonoidHom.snd PSL₂ C).comp e.toMonoidHom
  have := IsPerfect.ofSurjective (f := t) (Prod.snd_surjective.comp e.surjective)
  have := IsPerfect.subsingleton_of_isMulCommutative (G := C)
  have h1 := Nat.card_of_subsingleton (1 : C)
  omega

private theorem four_frattini : ∃ emb : center SL₂ →* C₄, Injective emb ∧
    emb.range ≤ frattini C₄ := by
  have hc : Nat.card C₄ = 4 := by simp [C₄, Nat.card_eq_fintype_card]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := C₄) 2 (n := 1) (by rw [hc]; decide)
  rw [pow_one] at hK
  let e : center SL₂ ≃* K := mulEquivOfPrimeCardEq center_card hK
  refine ⟨K.subtype.comp e.toMonoidHom, K.subtype_injective.comp e.injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
    range_subtype]
  apply le_iInf₂
  intro M hm
  have h2 : IsPGroup 2 C₄ := IsPGroup.of_card (n := 2) hc
  have hi := h2.isCoatom_iff_index_eq_prime.mp hm
  have h := M.index_mul_card
  rw [hi, hc] at h
  exact IsCyclic.subgroup_le_iff_card_dvd.mpr (by rw [hK, show Nat.card M = 2 by omega])

private theorem radical_of_projection (p : G →* PSL₂) (hp : Surjective p) (R : Subgroup G)
    (hr : p.ker = R) [Group.IsSolvable R] : IsSolubleRadical R := by
  refine ⟨hr ▸ inferInstanceAs p.ker.Normal, inferInstance, ?_⟩
  intro N hn hs
  have := hn.map p hp
  rw [← hr, ← Subgroup.map_eq_bot_iff]
  apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map p)).resolve_right
  intro he
  have hsurj : Surjective (p.domRestrict N) := MonoidHom.range_eq_top.mp
    ((MonoidHom.domRestrict_range ..).trans he)
  exact IsPerfect.not_isSolvable (G := PSL₂) (Group.isSolvable_of_surjective hsurj)

private theorem class_not_composition : ¬ IsComposition (residualClass PSL₂) := by
  classical
  obtain ⟨emb, hinj, hphi⟩ := four_frattini
  -- Identify the central involution of the cover with the involution of the cyclic group.
  let d := (center SL₂).subtype.prod emb
  have : d.range.Normal := normal_of_le_center (H := d.range) (by
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.center_prod]
    exact ⟨z.property, mem_center_iff.mpr fun _ => mul_comm ..⟩)
  let G := (SL₂ × C₄) ⧸ d.range
  let π := QuotientGroup.mk' d.range
  let i := π.comp (MonoidHom.inl SL₂ C₄)
  let j := π.comp (MonoidHom.inr SL₂ C₄)
  have hi : Injective i := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff (x, (1 : C₄))).mp hx
    have he : emb z = 1 := congrArg Prod.snd hz
    have hz1 := ((injective_iff_map_eq_one emb).mp hinj) z he
    exact (congrArg Prod.fst hz).symm.trans (congrArg Subtype.val hz1)
  let R := j.range
  have hj (z : center SL₂) : i z * j (emb z) = 1 := by
    change π (z.val, 1) * π (1, emb z) = 1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨z, by simp [d]⟩
  -- Projection to the simple quotient identifies the cyclic factor as the whole soluble radical.
  let p₀ := (QuotientGroup.mk' (center SL₂)).comp (MonoidHom.fst SL₂ C₄)
  have hd : d.range ≤ p₀.ker := by
    rintro _ ⟨z, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr z.property
  let p : G →* PSL₂ := QuotientGroup.lift d.range p₀ hd
  have hp : Surjective p := QuotientGroup.lift_surjective_of_surjective d.range p₀
    ((QuotientGroup.mk'_surjective (center SL₂)).comp Prod.fst_surjective) hd
  have hker : p.ker = R := by
    apply le_antisymm
    · intro g hg
      obtain ⟨⟨x, c⟩, rfl⟩ := QuotientGroup.mk'_surjective d.range g
      have hx : x ∈ center SL₂ := (QuotientGroup.eq_one_iff x).mp hg
      let z : center SL₂ := ⟨x, hx⟩
      refine ⟨(emb z)⁻¹ * c, ?_⟩
      rw [map_mul, map_inv, ← eq_inv_of_mul_eq_one_left (hj z)]
      change π (x, 1) * π (1, c) = π (x, c)
      rw [← map_mul]; simp
    · rintro _ ⟨c, rfl⟩
      exact map_one (QuotientGroup.mk' (center SL₂))
  have : Group.IsSolvable R := Group.isSolvable_of_surjective j.rangeRestrict_surjective
  have hR := radical_of_projection p hp R hker
  let F := (frattini R).map R.subtype
  have := hR.1
  let q := QuotientGroup.mk' F
  -- In the Frattini quotient the homomorphism from the cover descends to the simple group.
  have hkill : center SL₂ ≤ (q.comp i).ker := by
    intro x hx
    let z : center SL₂ := ⟨x, hx⟩
    have hm : j.rangeRestrict (emb z) ∈ frattini R :=
      frattini_le_comap_frattini_of_surjective j.rangeRestrict_surjective (hphi ⟨z, rfl⟩)
    have hmem : j (emb z) ∈ F := ⟨_, hm, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact eq_inv_of_mul_eq_one_left (hj z) ▸ F.inv_mem hmem
  let a := QuotientGroup.lift (center SL₂) (q.comp i) hkill
  let b := q.comp j
  have hab : ∀ x y, Commute (a x) (b y) := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ((MonoidHom.commute_inl_inr x y).map π).map q
  let t := a.noncommCoprod b hab
  have ht : Surjective t := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective F y
    obtain ⟨⟨x, c⟩, rfl⟩ := QuotientGroup.mk'_surjective d.range g
    refine ⟨(QuotientGroup.mk' _ x, c), ?_⟩
    change q (π (x, 1)) * q (π (1, c)) = q (π (x, c))
    rw [← map_mul, ← map_mul]; simp
  have hsimple : (residualClass PSL₂).mem PSL₂ := ⟨0, generated_self⟩
  have hquot := class_map t ht (class_prod hsimple (class_of_soluble (G := C₄)))
  intro h
  have hg := h G R hR ⟨inferInstance, hquot⟩
  have him := class_hereditary minimal_simple G i.range hg
  exact cover_outside ((residualClass PSL₂).iso _ _ (MonoidHom.ofInjective hi).symm him)

/--
**Radical hereditary formations need not be composition formations.** It is not true that every
radical hereditary formation of finite groups is a composition formation: some class of groups
that is a formation, a radical class and a hereditary class is not solubly saturated.

Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.7 (A. F. Vasil'ev); resolution: S.
F. Kamornikov, Math. Notes 55 (1994), no. 6, 586-588, Kourovka Archive, Problem 12.7: No, it is not.
-/
theorem radicalHereditaryFormationIsComposition_refuted :
    ¬ radicalHereditaryFormationIsComposition := by
  intro h
  exact class_not_composition (h (residualClass PSL₂) (class_formation minimal_simple)
    (class_radical minimal_simple) (class_hereditary minimal_simple))

end MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted
