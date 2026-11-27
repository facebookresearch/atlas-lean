/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.Order.Minimal
import Mathlib.Order.RelSeries

/-!
# Formations of groups with all composition factors `T` (Kourovka Notebook Problem 12.97)

Kourovka Notebook, Archive of Solved Problems, Problem 12.97 (L. A. Shemetkov): let `𝔉` be the
formation of all finite groups all of whose composition factors are isomorphic to a fixed
non-abelian simple group `T`. Mel'nikov proved that `𝔉` is not a product of two non-trivial
proper subformations.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.97 (L. A.
Shemetkov). UnsolvedMath record UM-00700914 (`KOU-12.97`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. `G ∈ 𝔉_T` means a subnormal series with all factors isomorphic to `T` (for
simple `T`, all composition factors isomorphic to `T`; the trivial group belongs). A formation
contains the trivial group and is closed under quotients and subdirect products; the product is
Gaschütz's `𝔐ℌ = {G | G^ℌ ∈ 𝔐}` with `G^ℌ` the `ℌ`-residual; subformations are contained in `𝔉_T`.
Non-trivial factors are proper subformations containing a nontrivial group: since `𝔉_T` is closed
under normal subgroups and extensions, `𝔉_T = 𝔉_T ℌ = 𝔐 𝔉_T` for all subformations `𝔐, ℌ`, so with
`𝔐 = 𝔉_T` or `ℌ = 𝔉_T` allowed the statement would be false.

## Proof

For a proper subformation `H`, every group in `𝔉_T` occurs as a quotient of the `H`-residual of
some group in `𝔉_T`. The proof lifts a residual quotient through a wreath product and inducts on
group order using a minimal normal subgroup. Thus a formation containing all these residuals
contains all of `𝔉_T`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97Wanted

/-- **Isomorphism-closed classes of groups (Kourovka 12.97).** A class of groups is given by a
membership predicate on groups such that every group isomorphic to a member is again a member.
Only the finite members matter in the formulation of Kourovka Problem 12.97. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Formations of finite groups (Kourovka 12.97).** A class $X$ of groups is a formation when it
contains the trivial group, the quotient $G/N$ lies in $X$ for every finite group $G$ in $X$ and
every normal subgroup $N$ of $G$, and for every finite group $G$ with normal subgroups $N_1$ and
$N_2$ such that $G/N_1$ and $G/N_2$ lie in $X$, the quotient $G/(N_1 \cap N_2)$ lies in $X$. -/
def IsFormation (X : GroupClass) : Prop :=
  X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- **Classes containing a nontrivial finite group.** A class $X$ of groups is nontrivial when it
contains a nontrivial finite group; for a formation this means that $X$ is not the trivial
formation. -/
def NontrivialClass (X : GroupClass) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ X.mem G

/-- **The residual of a group with respect to a class (Kourovka 12.97).** For a class $X$ of groups
and a group $G$, the $X$-residual of $G$ is the intersection of all normal subgroups $N$ of $G$
such that the quotient $G/N$ lies in $X$. -/
def residual (X : GroupClass) (G : Type) [Group G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : ∃ _ : N.Normal, X.mem (G ⧸ N)), N

/-- **Groups with a subnormal series whose factors are all isomorphic to a given group.** For
groups $T$ and $G$, the group $G$ lies in the class $\mathfrak{F}_T$ when it has a subnormal series
$1 = H_0 \le H_1 \le \dots \le H_n = G$, each $H_i$ normal in $H_{i+1}$, all of whose factors
$H_{i+1}/H_i$ are isomorphic to $T$. For simple $T$ these are the groups all of whose composition
factors are isomorphic to $T$. -/
def AllCompositionFactorsIso (T : Type) [Group T] (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        Nonempty ((H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ≃* T)

/-- `X` is a proper subclass of `𝔉_T`: some finite group of `𝔉_T` does not belong to `X`. -/
def IsProperIn (T : Type) [Group T] (X : GroupClass) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), AllCompositionFactorsIso T G ∧ ¬ X.mem G

/-- **Kourovka Problem 12.97 (Shemetkov).** For a group $T$, write $\mathfrak{F}_T$ for the class
of groups having a subnormal series all of whose factors are isomorphic to $T$. This is the
proposition that, for every finite non-abelian simple group $T$ and all formations $\mathfrak{M}$
and $\mathfrak{H}$ whose finite members lie in $\mathfrak{F}_T$, each containing a nontrivial
finite group and each missing some finite group of $\mathfrak{F}_T$, it is not the case that every
finite group $G$ satisfies: $G \in \mathfrak{F}_T$ if and only if the $\mathfrak{H}$-residual
$G^{\mathfrak{H}}$ of $G$ lies in $\mathfrak{M}$. In other words, $\mathfrak{F}_T$ is not the
Gaschütz product $\mathfrak{M}\mathfrak{H} = \{G : G^{\mathfrak{H}} \in \mathfrak{M}\}$ of two
nontrivial proper subformations. -/
def compositionFactorFormationIndecomposable : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    ∀ M H : GroupClass, IsFormation M → IsFormation H → NontrivialClass M →
      NontrivialClass H →
      (∀ (G : Type) [Group G] [Finite G], M.mem G → AllCompositionFactorsIso T G) →
      (∀ (G : Type) [Group G] [Finite G], H.mem G → AllCompositionFactorsIso T G) →
      IsProperIn T M → IsProperIn T H →
      ¬ ∀ (G : Type) [Group G] [Finite G], AllCompositionFactorsIso T G ↔ M.mem (residual H G)

open Function Relation

variable {T G D : Type} [Group T] [Group G] [Group D]

/-- One step of a series, described by an epimorphism onto the prescribed factor. -/
private def Step (T : Type) [Group T] (A B : Subgroup G) : Prop :=
  A ≤ B ∧ ∃ f : B →* T, Surjective f ∧ f.ker = A.subgroupOf B

private abbrev Chain (T : Type) [Group T] (A B : Subgroup G) :=
  ReflTransGen (Step T) A B

private theorem chain_iff :
    AllCompositionFactorsIso T G ↔ Chain T (⊥ : Subgroup G) ⊤ := by
  constructor
  · rintro ⟨n, K, h0, hn, hs⟩
    have h (i : Fin (n + 1)) : Chain T (K 0) (K i) := by
      induction i using Fin.induction with
      | zero => exact .refl
      | succ i ih =>
        obtain ⟨h, hN, ⟨e⟩⟩ := hs i
        let q := QuotientGroup.mk' ((K i.castSucc).subgroupOf (K i.succ))
        refine ih.tail ⟨h, e.toMonoidHom.comp q,
          e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
        ext x
        simp [q]
    simpa only [h0, hn] using h (Fin.last n)
  · intro hc
    let r : SetRel (Subgroup G) (Subgroup G) := {p | Step T p.1 p.2}
    have build {A B : Subgroup G} (h : Chain T A B) :
        ∃ s : RelSeries r, s.head = A ∧ s.last = B := by
      induction h with
      | refl => exact ⟨.singleton _ _, rfl, rfl⟩
      | tail h hab ih =>
        obtain ⟨s, hs, hl⟩ := ih
        exact ⟨s.snoc _ (hl.symm ▸ hab), by simpa using hs, by simp⟩
    obtain ⟨s, h0, hl⟩ := build hc
    refine ⟨s.length, s, h0, hl, fun i ↦ ?_⟩
    obtain ⟨hle, f, hf, hk⟩ := s.step i
    refine ⟨hle, ?_⟩
    rw [← hk]
    exact ⟨f.normal_ker, ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

private theorem chain_map_of {A B : Subgroup G} (h : Chain T A B)
    (F : Subgroup G → Subgroup D)
    (hf : ∀ {K L}, Step T K L → Chain T (F K) (F L)) : Chain T (F A) (F B) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (hf hs)

private theorem step_comap (p : D →* G) (hp : Surjective p)
    {A B : Subgroup G} (h : Step T A B) : Step T (A.comap p) (B.comap p) := by
  obtain ⟨hab, f, hf, hk⟩ := h
  refine ⟨Subgroup.comap_mono hab, f.comp (p.subgroupComap B),
    hf.comp (p.subgroupComap_surjective B hp), ?_⟩
  ext x
  exact (SetLike.ext_iff.mp hk (p.subgroupComap B x))

private theorem step_map_inj (p : G →* D) (hp : Injective p)
    {A B : Subgroup G} (h : Step T A B) : Step T (A.map p) (B.map p) := by
  obtain ⟨hab, f, hf, hk⟩ := h
  let e := B.equivMapOfInjective p hp
  refine ⟨Subgroup.map_mono hab, f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  change f (e.symm (e x)) = 1 ↔ p x ∈ A.map p
  rw [e.symm_apply_apply, Subgroup.mem_map_iff_mem hp]
  exact SetLike.ext_iff.mp hk x

private theorem factors_ext (p : G →* D) (hp : Surjective p)
    (hK : AllCompositionFactorsIso T p.ker) (hD : AllCompositionFactorsIso T D) :
    AllCompositionFactorsIso T G := by
  apply chain_iff.mpr
  have hk := chain_map_of (chain_iff.mp hK) (Subgroup.map p.ker.subtype)
    (fun hs ↦ .single (step_map_inj _ Subtype.val_injective hs))
  have hd := chain_map_of (chain_iff.mp hD) (Subgroup.comap p)
    (fun hs ↦ .single (step_comap p hp hs))
  have lower : Chain T (⊥ : Subgroup G) p.ker := by simpa [Subgroup.map_top] using hk
  exact lower.trans (by simpa using hd)

private theorem factors_iso (h : AllCompositionFactorsIso T G) (e : G ≃* D) :
    AllCompositionFactorsIso T D := by
  have hd := chain_map_of (chain_iff.mp h) (Subgroup.map e.toMonoidHom)
    (fun hs ↦ .single (step_map_inj _ e.injective hs))
  apply chain_iff.mpr
  simpa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hd

private theorem factors_trivial [Subsingleton G] : AllCompositionFactorsIso T G := by
  apply chain_iff.mpr
  rw [Subsingleton.elim (⊥ : Subgroup G) ⊤]

-- Under a homomorphism, a simple factor either survives or collapses to a repeated subgroup.
private theorem step_map [IsSimpleGroup T] (p : G →* D)
    {A B : Subgroup G} (h : Step T A B) : Chain T (A.map p) (B.map p) := by
  obtain ⟨hab, f, hf, hk⟩ := h
  let g := p.subgroupMap B
  have hg : Surjective g := p.subgroupMap_surjective B
  have hn := Subgroup.Normal.map g.normal_ker f hf
  rcases hn.eq_bot_or_eq_top with he | he
  · have hle : g.ker ≤ f.ker := by
      intro x hx
      exact (show f x ∈ (⊥ : Subgroup T) from he ▸ Subgroup.mem_map_of_mem f hx)
    let d := g.liftOfSurjective hg ⟨f, hle⟩
    have hd (x : B) : d (g x) = f x := g.liftOfRightInverse_comp_apply _ _ _ _
    refine .single ⟨Subgroup.map_mono hab, d, ?_, ?_⟩
    · intro t
      obtain ⟨x, rfl⟩ := hf t
      exact ⟨g x, hd x⟩
    · ext y
      obtain ⟨x, rfl⟩ := hg y
      change d (g x) = 1 ↔ p x ∈ A.map p
      constructor
      · intro hx
        exact Subgroup.mem_map_of_mem _ ((SetLike.ext_iff.mp hk x).mp ((hd x).symm.trans hx))
      · rintro ⟨a, ha, heq⟩
        have hg' : g x = g ⟨a, hab ha⟩ := Subtype.ext heq.symm
        rw [hg', hd]
        exact (SetLike.ext_iff.mp hk _).mpr ha
  · have eq : A.map p = B.map p := by
      apply le_antisymm (Subgroup.map_mono hab)
      rintro _ ⟨x, hx, rfl⟩
      let b : B := ⟨x, hx⟩
      obtain ⟨y, hy, hy'⟩ : f b ∈ g.ker.map f := he ▸ Subgroup.mem_top _
      have hz : b / y ∈ f.ker := by simp [MonoidHom.mem_ker, hy']
      have hzy := (SetLike.ext_iff.mp hk _).mp hz
      refine ⟨↑(b / y), hzy, ?_⟩
      have hone : p y = 1 := congrArg Subtype.val (show g y = 1 from hy)
      simp [b, hone]
    rw [eq]

private theorem factors_image [IsSimpleGroup T] (h : AllCompositionFactorsIso T G)
    (p : G →* D) (hp : Surjective p) : AllCompositionFactorsIso T D := by
  have hd := chain_map_of (chain_iff.mp h) (Subgroup.map p) (step_map p)
  exact chain_iff.mpr (by simpa [Subgroup.map_top_of_surjective p hp] using hd)

private theorem factors_normal [IsSimpleGroup T] (h : AllCompositionFactorsIso T G)
    (N : Subgroup G) [N.Normal] : AllCompositionFactorsIso T N := by
  have hr := chain_map_of (chain_iff.mp h) (fun K ↦ K.subgroupOf N) (fun {A B} hs ↦ ?_)
  · apply chain_iff.mpr
    simpa using hr
  obtain ⟨hab, f, hf, hk⟩ := hs
  let g := N.subtype.subgroupComap B
  have hrange : g.range = N.subgroupOf B := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.val.property, fun hx ↦ ⟨⟨⟨x, hx⟩, x.property⟩, rfl⟩⟩
  have hn := Subgroup.Normal.map (show g.range.Normal from hrange ▸ inferInstance) f hf
  have hr' : (f.comp g).range = g.range.map f := MonoidHom.range_comp _ _
  rcases hn.eq_bot_or_eq_top with he | he
  · have eq : A.subgroupOf N = B.subgroupOf N := by
      apply le_antisymm (Subgroup.comap_mono hab)
      intro x hx
      have hz : f (g ⟨x, hx⟩) ∈ (⊥ : Subgroup T) := by
        rw [← he, ← hr']
        exact ⟨_, rfl⟩
      exact (SetLike.ext_iff.mp hk _).mp hz
    rw [eq]
  · refine .single ⟨Subgroup.comap_mono hab, f.comp g,
      MonoidHom.range_eq_top.mp (hr'.trans he), ?_⟩
    ext x
    exact SetLike.ext_iff.mp hk (g x)

private theorem factors_exact {K : Type} [Group K] (i : K →* G) (hi : Injective i)
    (p : G →* D) (hp : Surjective p) (hk : i.range = p.ker)
    (hK : AllCompositionFactorsIso T K) (hD : AllCompositionFactorsIso T D) :
    AllCompositionFactorsIso T G := by
  exact factors_ext p hp (hk ▸ factors_iso hK (MonoidHom.ofInjective hi)) hD

private theorem factors_prod (hG : AllCompositionFactorsIso T G)
    (hD : AllCompositionFactorsIso T D) : AllCompositionFactorsIso T (G × D) := by
  apply factors_exact (MonoidHom.inl G D) (fun _ _ h ↦ congrArg Prod.fst h)
    (MonoidHom.snd G D) (fun x ↦ ⟨(1, x), rfl⟩) _ hG hD
  ext x
  change (∃ y, (y, 1) = x) ↔ x.2 = 1
  simp [Prod.ext_iff, eq_comm]

private theorem factors_power (hG : AllCompositionFactorsIso T G) (I : Type) [Finite I] :
    AllCompositionFactorsIso T (I → G) := by
  induction I using Finite.induction_empty_option with
  | of_equiv e ih =>
    exact factors_iso ih { toEquiv := e.arrowCongr (Equiv.refl G), map_mul' := fun _ _ ↦ rfl }
  | h_empty => exact factors_trivial
  | h_option ih =>
    apply factors_iso (factors_prod hG ih)
    exact { toEquiv := (Equiv.piOptionEquivProd (β := fun _ ↦ G)).symm, map_mul' := fun a b ↦ by
              funext i; cases i <;> rfl }

private theorem factors_epi_simple [Nontrivial G] (hG : AllCompositionFactorsIso T G) :
    ∃ f : G →* T, Surjective f := by
  have h := (chain_iff.mp hG).cases_tail
  rcases h with he | ⟨K, _, _, f, hf, _⟩
  · exact (top_ne_bot he).elim
  · let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
    exact ⟨f.comp e.toMonoidHom, hf.comp e.surjective⟩

variable {X : GroupClass}

private theorem formation_image (hX : IsFormation X) [Finite G] (p : G →* D)
    (hp : Surjective p) (hg : X.mem G) : X.mem D :=
  X.iso _ _ (QuotientGroup.quotientKerEquivOfSurjective p hp) (hX.2.1 G p.ker hg)

private theorem residual_le (N : Subgroup G) [N.Normal] (h : X.mem (G ⧸ N)) :
    residual X G ≤ N :=
  iInf_le_of_le N (iInf_le _ ⟨inferInstance, h⟩)

private instance residualNormal (X : GroupClass) (G : Type) [Group G] : (residual X G).Normal :=
  Subgroup.normal_iInf_normal fun _ ↦ Subgroup.normal_iInf_normal fun ⟨h, _⟩ ↦ h

private theorem residual_quotient (hX : IsFormation X) (G : Type) [Group G] [Finite G] :
    X.mem (G ⧸ residual X G) := by
  let S (N : Subgroup G) := ∃ _ : N.Normal, X.mem (G ⧸ N)
  have htop : S ⊤ := by
    have := QuotientGroup.subsingleton_quotient_top (G := G)
    let : Unique (G ⧸ (⊤ : Subgroup G)) := uniqueOfSubsingleton 1
    exact ⟨inferInstance, X.iso Unit _ MulEquiv.ofUnique hX.1⟩
  obtain ⟨N, ⟨hN, hn⟩, hmin⟩ := exists_minimal_of_wellFoundedLT S ⟨⊤, htop⟩
  have eq : N = residual X G := by
    refine le_antisymm (le_iInf fun K ↦ le_iInf fun ⟨hK, hk⟩ ↦ ?_) (residual_le N hn)
    have hh : S (N ⊓ K) := ⟨inferInstance, hX.2.2 G N K hn hk⟩
    exact (hmin hh inf_le_left).trans inf_le_right
  subst N
  exact hn

private theorem residual_le_ker [Finite G] (p : G →* D) (hp : Surjective p) (hd : X.mem D) :
    residual X G ≤ p.ker :=
  residual_le _ (X.iso _ _ (QuotientGroup.quotientKerEquivOfSurjective p hp).symm hd)

private theorem residual_map (hX : IsFormation X) [Finite G] [Finite D] (p : G →* D)
    (hp : Surjective p) : (residual X G).map p = residual X D := by
  let R := residual X G
  let S := R.map p
  have hS := Subgroup.Normal.map (inferInstance : R.Normal) p hp
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    let q := QuotientGroup.mk' (residual X D)
    have h := residual_le_ker (X := X) (q.comp p) ((QuotientGroup.mk'_surjective _).comp hp)
      (residual_quotient hX D)
    exact fun x hx ↦ (QuotientGroup.eq_one_iff (p x)).mp (h hx)
  · apply residual_le S
    let q := QuotientGroup.mk' S
    have h : R ≤ (q.comp p).ker := fun x hx ↦ (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_map_of_mem p hx)
    let f := QuotientGroup.lift R (q.comp p) h
    apply formation_image hX f _ (residual_quotient hX G)
    intro y
    obtain ⟨x, rfl⟩ := ((QuotientGroup.mk'_surjective S).comp hp) y
    exact ⟨QuotientGroup.mk x, rfl⟩

private theorem factors_perfect [IsSimpleGroup T] (hn : ∃ a b : T, a * b ≠ b * a)
    (hg : AllCompositionFactorsIso T G) : Group.IsPerfect G := by
  apply Group.subsingleton_abelianization_iff_isPerfect.mp
  by_contra! h
  obtain ⟨f, hf⟩ := factors_epi_simple (factors_image hg (Group.Abelianization.of (G := G))
    (Group.Abelianization.surjective_of G))
  obtain ⟨a, b, hne⟩ := hn
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  exact hne (by rw [← map_mul, ← map_mul, mul_comm x y])

/-- A group realized as a quotient of an `X`-residual inside the composition-factor class. -/
private def Realized (T : Type) [Group T] (X : GroupClass) (A : Type) [Group A] : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), AllCompositionFactorsIso T G ∧
    ∃ f : residual X G →* A, Surjective f

private theorem realized_image (h : Realized T X G) (p : G →* D) (hp : Surjective p) :
    Realized T X D := by
  obtain ⟨B, _, _, hb, f, hf⟩ := h
  exact ⟨B, inferInstance, inferInstance, hb, p.comp f, hp.comp hf⟩

private theorem realized_prod [IsSimpleGroup T] (hn : ∃ a b : T, a * b ≠ b * a)
    (hX : IsFormation X) (hG : Realized T X G) (hD : Realized T X D) :
    Realized T X (G × D) := by
  obtain ⟨B, _, _, hb, f, hf⟩ := hG
  obtain ⟨C, _, _, hc, g, hg⟩ := hD
  let U := residual X (B × C)
  let B' := residual X B
  let C' := residual X C
  have hb' : U.map (MonoidHom.fst B C) = B' :=
    residual_map hX _ (fun b ↦ ⟨(b, 1), rfl⟩)
  have hc' : U.map (MonoidHom.snd B C) = C' :=
    residual_map hX _ (fun c ↦ ⟨(1, c), rfl⟩)
  let p : U →* B' := ((MonoidHom.fst B C).comp U.subtype).codRestrict B' fun x ↦
    hb' ▸ Subgroup.mem_map_of_mem _ x.property
  let q : U →* C' := ((MonoidHom.snd B C).comp U.subtype).codRestrict C' fun x ↦
    hc' ▸ Subgroup.mem_map_of_mem _ x.property
  have := factors_perfect hn (factors_normal hb B')
  -- Commutators of elements of U with (b', 1) put [B', B'] × 1 inside U. Since B' is
  -- perfect, this gives all of B' × 1.
  have hleft : B' ≤ U.comap (MonoidHom.inl B C) := by
    rw [← B'.commutator_eq_self]
    apply Subgroup.commutator_le.mpr
    intro b hb b' _
    obtain ⟨⟨_, c⟩, hc, rfl⟩ := (hb' ▸ hb : b ∈ U.map (MonoidHom.fst B C))
    have h := Subgroup.commutator_le_left U ⊤
      (Subgroup.commutator_mem_commutator hc (Subgroup.mem_top (b', (1 : C))))
    simpa [commutatorElement_def] using h
  refine ⟨B × C, inferInstance, inferInstance, factors_prod hb hc,
    (f.comp p).prod (g.comp q), ?_⟩
  rintro ⟨a, d⟩
  obtain ⟨b, rfl⟩ := hf a
  obtain ⟨c, rfl⟩ := hg d
  obtain ⟨⟨b₀, c₀⟩, hu, he⟩ := (hc' ▸ c.property : ↑c ∈ U.map (MonoidHom.snd B C))
  have hb₀ : b₀ ∈ B' := hb' ▸ Subgroup.mem_map_of_mem _ hu
  have hu' : (b.val, c.val) ∈ U := by
    have h := U.mul_mem (hleft (B'.div_mem b.property hb₀)) hu
    change (b.val / b₀ * b₀, 1 * c₀) ∈ U at h
    simpa [show c₀ = ↑c from he] using h
  exact ⟨⟨_, hu'⟩, rfl⟩

section Cover
variable {B Q A : Type} [Group B] [Group Q] [Group A]

/-- The change of representatives for multiplication by `b` in the quotient `Q`. -/
private def changeRep (q : B →* Q) (s : Q → B) (hs : RightInverse s q) (b : B) (x : Q) :
    q.ker :=
  ⟨(s x)⁻¹ * b * s ((q b)⁻¹ * x), by simp [MonoidHom.mem_ker, hs _, mul_assoc]⟩

private theorem changeRep_mul (q : B →* Q) (s : Q → B) (hs : RightInverse s q) (a b : B)
    (x : Q) : changeRep q s hs (a * b) x =
    changeRep q s hs a x * changeRep q s hs b ((q a)⁻¹ * x) := by
  apply Subtype.ext
  simp [changeRep, mul_assoc]

private def inducedMap (q : B →* Q) (s : Q → B) (hs : RightInverse s q) (u : q.ker →* D) :
    B →* D ≀ᵣ Q where
  toFun b := ⟨fun x ↦ u (changeRep q s hs b x), q b⟩
  map_one' := by
    apply RegularWreathProduct.ext _ (map_one q)
    funext x
    change u _ = 1
    rw [← u.map_one]
    congr 1
    exact Subtype.ext (by simp [changeRep])
  map_mul' a b := by
    apply RegularWreathProduct.ext _ (q.map_mul a b)
    funext x
    exact (congrArg u (changeRep_mul q s hs a b x)).trans (u.map_mul _ _)

private def wreathMap (v : A →* D) : A ≀ᵣ Q →* D ≀ᵣ Q where
  toFun w := ⟨v ∘ w.left, w.right⟩
  map_one' := RegularWreathProduct.ext (funext fun _ ↦ map_one v) rfl
  map_mul' _ _ := RegularWreathProduct.ext (funext fun _ ↦ map_mul v _ _) rfl

/-- Pull an epimorphism back along the induced map. Evaluation on the kernel of the
quotient map lifts the original epimorphism from that kernel. -/
private theorem induced_cover [Finite B] [Finite Q] [Finite A]
    (q : B →* Q) (hq : Surjective q) (u : q.ker →* D) (hu : Surjective u)
    (v : A →* D) (hv : Surjective v) (hb : AllCompositionFactorsIso T B)
    (hk : AllCompositionFactorsIso T v.ker) :
    ∃ (C : Type) (_ : Group C) (_ : Finite C), AllCompositionFactorsIso T C ∧
      ∃ (p : C →* B) (_ : Surjective p) (e : (q.ker.comap p) →* A), Surjective e ∧
        v.comp e = u.comp (p.subgroupComap q.ker) := by
  classical
  let s (x : Q) := surjInv hq x / surjInv hq 1
  have hs : RightInverse s q := fun x ↦ by simp [s, rightInverse_surjInv hq _]
  have hs1 : s 1 = 1 := by simp [s]
  let L := inducedMap q s hs u
  let W := A ≀ᵣ Q
  -- A point of the pullback is a lift in the wreath product together with its image in B.
  let C := ((wreathMap v).comp (MonoidHom.fst W B)).eqLocus (L.comp (MonoidHom.snd W B))
  let p := (MonoidHom.snd W B).comp C.subtype
  have mem (w : W) (b : B) : (w, b) ∈ C ↔
      (∀ x, v (w.left x) = u (changeRep q s hs b x)) ∧ w.right = q b := by
    change wreathMap v w = L b ↔ _
    rw [RegularWreathProduct.ext_iff, funext_iff]
    rfl
  have hp : Surjective p := by
    intro b
    let w : W := ⟨fun x ↦ surjInv hv (u (changeRep q s hs b x)), q b⟩
    exact ⟨⟨(w, b), (mem w b).mpr ⟨fun _ ↦ rightInverse_surjInv hv _, rfl⟩⟩, rfl⟩
  have one_rep (x : Q) : changeRep q s hs 1 x = 1 := Subtype.ext (by simp [changeRep])
  -- Over the identity of B each coordinate may be chosen independently in the kernel of v.
  let i : (Q → v.ker) →* C :=
    { toFun := fun a ↦ ⟨(⟨fun x ↦ a x, 1⟩, 1), (mem _ _).mpr
        ⟨fun x ↦ by rw [one_rep, map_one]; exact (a x).property, q.map_one.symm⟩⟩
      map_one' := rfl
      map_mul' := fun a b ↦ Subtype.ext (Prod.ext
        (RegularWreathProduct.ext (funext fun x ↦ by
          change (a x : A) * (b x : A) = (a x : A) * (b ((1 : Q)⁻¹ * x) : A)
          simp) (one_mul _).symm) (one_mul _).symm) }
  have hi : Injective i := by
    intro a b h
    exact funext fun x ↦ Subtype.ext (congrArg (fun z : C ↦ z.val.1.left x) h)
  have her : i.range = p.ker := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      rfl
    · intro hc
      have h : c.val.2 = 1 := hc
      obtain ⟨hl, hr⟩ := (mem _ _).mp c.property
      let a (x : Q) : v.ker := ⟨c.val.1.left x, by simpa [h, one_rep] using hl x⟩
      have hr1 : 1 = c.val.1.right := by simp [hr, h]
      exact ⟨a, Subtype.ext (Prod.ext (RegularWreathProduct.ext rfl hr1) h.symm)⟩
  -- On K the permutation of the coordinates is trivial, so evaluation at 1 is a homomorphism.
  let K := q.ker.comap p
  have right_one (z : K) : z.val.val.1.right = 1 :=
    ((mem _ _).mp z.val.property).2.trans z.property
  let e : K →* A :=
    { toFun := fun z ↦ z.val.val.1.left 1
      map_one' := rfl
      map_mul' := fun a b ↦ by
        change a.val.val.1.left 1 * b.val.val.1.left (a.val.val.1.right⁻¹ * 1) = _
        simp [right_one] }
  have rep_one (b : q.ker) : changeRep q s hs b 1 = b := by
    apply Subtype.ext
    simp [changeRep, hs1, show q b = 1 from b.property]
  have he : Surjective e := by
    intro a
    obtain ⟨b, hb⟩ := hu (v a)
    let w : W := ⟨fun x ↦ if x = 1 then a else surjInv hv (u (changeRep q s hs b x)), 1⟩
    have hw : (w, b.val) ∈ C := by
      apply (mem _ _).mpr
      refine ⟨fun x ↦ ?_, b.property.symm⟩
      by_cases h : x = 1
      · simpa [w, h, rep_one] using hb.symm
      · simp [w, h, rightInverse_surjInv hv _]
    exact ⟨⟨⟨_, hw⟩, b.property⟩, by simp [e, w]⟩
  refine ⟨C, inferInstance, inferInstance, factors_exact i hi p hp her (factors_power hk Q) hb,
    p, hp, e, he, ?_⟩
  ext z
  have h := ((mem _ _).mp z.val.property).1 1
  exact h.trans (congrArg u (rep_one (p.subgroupComap q.ker z)))

end Cover

/-- Given a realized quotient of `G`, realize a normal subgroup mapping onto that quotient. -/
private theorem lift_realized [IsSimpleGroup T] [Finite G] (hX : IsFormation X)
    (v : G →* D) (hv : Surjective v) (hg : AllCompositionFactorsIso T G)
    (hd : Realized T X D) :
    ∃ P : Subgroup G, P.Normal ∧ Realized T X P ∧ P.map v = ⊤ := by
  obtain ⟨B, _, _, hb, f, hf⟩ := hd
  let R := residual X B
  let q := QuotientGroup.mk' R
  let j : q.ker ≃* R := MulEquiv.subgroupCongr (QuotientGroup.ker_mk' R)
  let u := f.comp j.toMonoidHom
  obtain ⟨C, _, _, hc, p, hp, e, he, hcomm⟩ := induced_cover q
    (QuotientGroup.mk'_surjective R) u (hf.comp j.surjective) v hv hb (factors_normal hg v.ker)
  let S := residual X C
  have hmap : S.map p = q.ker := (residual_map hX p hp).trans (QuotientGroup.ker_mk' R).symm
  let K := q.ker.comap p
  have hSK : S ≤ K := Subgroup.map_le_iff_le_comap.mp hmap.le
  let P := (S.subgroupOf K).map e
  have hn := Subgroup.Normal.map (inferInstance : (S.subgroupOf K).Normal) e he
  let i := Subgroup.inclusion hSK
  let d := e.comp i
  have hd : d.range = P := by
    rw [MonoidHom.range_comp]
    change (Subgroup.inclusion hSK).range.map e = _
    rw [Subgroup.inclusion_range]
  have hP : Realized T X P := by
    rw [← hd]
    exact ⟨C, inferInstance, inferInstance, hc, d.rangeRestrict, d.rangeRestrict_surjective⟩
  refine ⟨P, hn, hP, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨r, rfl⟩ := (hf.comp j.surjective : Surjective u) x
  obtain ⟨c, h, hpc⟩ := (show ↑r ∈ S.map p by rw [hmap]; exact r.property)
  refine ⟨d ⟨c, h⟩, by rw [← hd]; exact ⟨_, rfl⟩, ?_⟩
  exact (DFunLike.congr_fun hcomm (i ⟨c, h⟩)).trans (congrArg u (Subtype.ext hpc))

private theorem realized_simple [IsSimpleGroup T] (hX : IsFormation X) (hprop : IsProperIn T X) :
    Realized T X T := by
  obtain ⟨B, _, _, hb, hx⟩ := hprop
  have hR : residual X B ≠ ⊥ := by
    intro he
    have h := residual_quotient hX B
    exact hx (X.iso _ _ ((QuotientGroup.quotientMulEquivOfEq he).trans
      QuotientGroup.quotientBot) h)
  have := (Subgroup.nontrivial_iff_ne_bot _).mpr hR
  exact ⟨B, inferInstance, inferInstance, hb, factors_epi_simple (factors_normal hb _)⟩

private theorem all_realized [IsSimpleGroup T] {G : Type} [Group G] [Finite G]
    (hn : ∃ a b : T, a * b ≠ b * a) (hX : IsFormation X) (ht : Realized T X T)
    (hg : AllCompositionFactorsIso T G) : Realized T X G := by
  classical
  rcases subsingleton_or_nontrivial G with h | h
  · exact realized_image ht (1 : T →* G) (fun x ↦ ⟨1, Subsingleton.elim _ _⟩)
  obtain ⟨f, hf⟩ := factors_epi_simple hg
  by_cases hinj : Injective f
  · let e := MulEquiv.ofBijective f ⟨hinj, hf⟩
    exact realized_image ht e.symm.toMonoidHom e.symm.surjective
  have hker : f.ker ≠ ⊥ := fun h ↦ hinj ((MonoidHom.ker_eq_bot_iff _).mp h)
  obtain ⟨N, hNK, ⟨hN, hnb⟩, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K : Subgroup G ↦ K.Normal ∧ K ≠ ⊥) f.ker ⟨f.normal_ker, hker⟩
  have hnt : N ≠ ⊤ := by
    intro he
    have hh : f.ker = ⊤ := top_unique (he ▸ hNK)
    obtain ⟨x, hx⟩ := exists_ne (1 : T)
    obtain ⟨a, rfl⟩ := hf x
    exact hx (show a ∈ f.ker from hh ▸ Subgroup.mem_top _)
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hquot : Nat.card (G ⧸ N) < Nat.card G := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    exact lt_mul_of_one_lt_right Nat.card_pos (N.one_lt_card_iff_ne_bot.mpr hnb)
  have hsub : Nat.card N < Nat.card G := by
    simpa using Subgroup.card_lt_of_lt hnt.lt_top
  have hd := all_realized hn hX ht (factors_image hg q hq)
  obtain ⟨P, hP, hp, hsur⟩ := lift_realized hX q hq hg hd
  by_cases he : P = ⊤
  · subst P
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    exact realized_image hp e.toMonoidHom e.surjective
  have hsup : N ⊔ P = ⊤ := by
    have eq := congrArg (Subgroup.comap q) hsur
    simpa [q, Subgroup.comap_map_eq, sup_comm] using eq
  have hdis : Disjoint N P := by
    apply disjoint_iff.mpr
    by_contra h
    have hle : N ≤ N ⊓ P := hmin ⟨inferInstance, h⟩ inf_le_left
    exact he ((sup_eq_right.mpr (hle.trans inf_le_right)).symm.trans hsup)
  -- The minimal normal subgroup and its proper normal supplement now form a direct product.
  have hr := all_realized hn hX ht (factors_normal hg N)
  let m := N.subtype.noncommCoprod P.subtype fun n p ↦
    Subgroup.commute_of_normal_of_disjoint N P hN hP hdis _ _ n.property p.property
  apply realized_image (realized_prod hn hX hr hp) m
  intro a
  obtain ⟨n, hn, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp
    (show a ∈ N ⊔ P from hsup ▸ Subgroup.mem_top _)
  exact ⟨(⟨n, hn⟩, ⟨p, hp⟩), rfl⟩
termination_by Nat.card G

/--
**Mel'nikov's theorem on Kourovka Problem 12.97.** Let $T$ be a finite non-abelian simple group,
and write $\mathfrak{F}_T$ for the class of groups having a subnormal series all of whose factors
are isomorphic to $T$. Let $\mathfrak{M}$ and $\mathfrak{H}$ be formations whose finite members
lie in $\mathfrak{F}_T$, each containing a nontrivial finite group and each missing some finite
group of $\mathfrak{F}_T$. Then it is not true that, for every finite group $G$, $G$ lies in
$\mathfrak{F}_T$ if and only if its $\mathfrak{H}$-residual $G^{\mathfrak{H}}$ lies in
$\mathfrak{M}$: the formation $\mathfrak{F}_T$ is not the Gaschütz product
$\mathfrak{M}\mathfrak{H}$ of two nontrivial proper subformations.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 12.97 (L. A. Shemetkov); resolution: O. V. Mel'nikov, Problems
in Algebra 9, Gomel', 1996, 42-47 (Russian), Kourovka Archive, Problem 12.97: it is proved.
-/
public theorem compositionFactorFormationIndecomposable_holds :
    compositionFactorFormationIndecomposable := by
  intro T _ _ _ hn M H hM hH _ _ _ _ hPM hPH heq
  obtain ⟨A, _, _, ha, hm⟩ := hPM
  obtain ⟨G, _, _, hg, f, hf⟩ := all_realized hn hH (realized_simple hH hPH) ha
  exact hm (formation_image hM f hf ((heq G).mp hg))

end MathlibExt.GroupTheory.SimpleCompositionFactorFormationKourovka12Problem97Wanted
