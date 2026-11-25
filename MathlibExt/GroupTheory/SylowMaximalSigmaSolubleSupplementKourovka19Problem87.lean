/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Sylow
public import MathlibExt.GroupTheory.SigmaSubnormal
import Mathlib.GroupTheory.GroupAction.Quotient
import MathlibExt.GroupTheory.BurnsidePaqb

/-!
# σ-soluble supplements to maximal subgroups of Sylow subgroups (Kourovka Notebook Problem 19.87)

Kourovka Notebook, Archive of Solved Problems, Problem 19.87 (A. N. Skiba): suppose that for every
Sylow subgroup `P` of a finite group `G` and every maximal subgroup `V` of `P` there is a
`σ`-soluble subgroup `T` such that `V T = G`. Is it true that then `G` is `σ`-soluble?

The answer is yes: `sylowMaximalSigmaSolubleSupplement_holds` proves the statement
`sylowMaximalSigmaSolubleSupplement` for every partition `σ` of the primes.

## Proof

The argument follows the minimal counterexample in the proof of Theorem A (i) of A.-M. Liu,
W. Guo, I. N. Safonova and A. N. Skiba, *A $G$-covering subgroup system of a finite group for some
classes of σ-soluble groups*, arXiv:2101.00247 (2021), up to its claims (*) and (**). The paper
finishes with Du's criterion for `π`-separability; here a sharper form of claim (**) leaves only two
primes, and Burnside's `p^a q^b` theorem (`BurnsidePaqb.burnside_paqb`) finishes. Let `G` be a
counterexample of least order.

* The hypothesis passes to every quotient `G / K`, and a group with a `σ`-primary normal subgroup
  `K` and `σ`-soluble quotient `G / K` is `σ`-soluble; so `G` has no nontrivial normal `σ`-primary
  subgroup (claim (*)).
* For a prime `q` dividing `|G|`, a supplement `T` of a maximal subgroup of a Sylow `q`-subgroup has
  `q`-power index. A minimal normal subgroup `R` of `T` is a `σᵢ`-group. If a prime `r ≠ q`
  dividing `|G|` were outside `σᵢ`, then `R` would lie in a `σ`-soluble supplement `T'` of `r`-power
  index, hence in the normal core of `T'`, which would contain a nontrivial normal `σ`-primary
  subgroup of `G`. So `σᵢ` contains every prime divisor of `|G|` except `q`.
* Comparing two primes, `|G|` has exactly two prime divisors, so `G` is solvable by Burnside's
  theorem and has a nontrivial normal subgroup of prime power order, a contradiction.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SylowMaximalSigmaSolubleSupplementKourovka19Problem87Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.87 (A. N.
Skiba). UnsolvedMath record UM-00701635 (`KOU-19.87`), dataset ulamai/UnsolvedMath v1.8.0.

A partition `σ` of the primes is a family `σ : I → Set ℕ` of nonempty, pairwise disjoint sets of
primes covering all primes; a positive integer (a finite group) is `σ`-primary when its prime
divisors (those of its order) lie in one block `σᵢ`. `σ`-soluble: every chief factor `A / B` (normal
`B < A` with no normal subgroup strictly between) is `σ`-primary, i.e. `|A : B|` is. Maximal
subgroups of `P` are the subgroups covered by `P` (`V ⋖ P`); `V T = G` means every element is `v t`.
Every partition `σ` is quantified. The `σ`-definitions are the shared ones in
`MathlibExt/GroupTheory/SigmaSubnormal.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Kourovka Problem 19.87 (statement).** The statement that for every partition $\sigma$ of the
set of all primes and every finite group $G$: if for every prime $p$, every Sylow $p$-subgroup $P$
of $G$ and every maximal subgroup $V$ of $P$ there is a $\sigma$-soluble subgroup $T$ of $G$ with
$VT = G$, that is, every element of $G$ is a product $vt$ with $v \in V$ and $t \in T$, then $G$ is
$\sigma$-soluble. Here a partition of the primes is a family of nonempty, pairwise disjoint sets of
primes whose union is the set of all primes, and a group is $\sigma$-soluble when for every chief
factor $A/B$ of it (normal subgroups $B < A$ with no normal subgroup strictly between them) all
prime divisors of the index $|A : B|$ lie in a single block of $\sigma$. -/
def sylowMaximalSigmaSolubleSupplement : Prop :=
  ∀ (I : Type) (σ : I → Set ℕ), IsPrimePartition σ → ∀ (G : Type) [Group G] [Finite G],
    (∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) →
      ∃ T : Subgroup G, IsSigmaSoluble σ T ∧ ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g) →
    IsSigmaSoluble σ G

/-! ### σ-primary numbers and σ-soluble groups -/

/-- A divisor of a `σ`-primary number is `σ`-primary. -/
private theorem isSigmaPrimary_of_dvd {I : Type} {σ : I → Set ℕ} {m n : ℕ}
    (h : IsSigmaPrimary σ n) (hmn : m ∣ n) : IsSigmaPrimary σ m := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun p hp hpm => hi p hp (hpm.trans hmn)⟩

/-- A prime power is `σ`-primary. -/
private theorem isSigmaPrimary_prime_pow {I : Type} {σ : I → Set ℕ} (hσ : IsPrimePartition σ)
    {p n : ℕ} (hp : p.Prime) : IsSigmaPrimary σ (p ^ n) := by
  obtain ⟨i, hi⟩ := hσ.2.2 p hp
  exact ⟨i, fun r hr hrd => (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrd) ▸ hi⟩

/-- A group of `σ`-primary order is `σ`-soluble. -/
private theorem isSigmaSoluble_of_isSigmaPrimary {I : Type} {σ : I → Set ℕ} {G : Type*}
    [Group G] (h : IsSigmaPrimary σ (Nat.card G)) : IsSigmaSoluble σ G := by
  intro A B _
  exact isSigmaPrimary_of_dvd h
    ((Subgroup.relIndex_dvd_card B A).trans (Subgroup.card_subgroup_dvd_card A))

/-- Homomorphic images of `σ`-soluble groups are `σ`-soluble. -/
private theorem isSigmaSoluble_of_surjective {I : Type} {σ : I → Set ℕ} {G H : Type*} [Group G]
    [Group H] {f : G →* H} (hf : Function.Surjective f) (hG : IsSigmaSoluble σ G) :
    IsSigmaSoluble σ H := by
  rintro A B ⟨hA, hB, hlt, hmax⟩
  have key : IsChiefFactor (A.comap f) (B.comap f) := by
    refine ⟨hA.comap f, hB.comap f, (Subgroup.comap_lt_comap_of_surjective hf).mpr hlt, ?_⟩
    intro N hN hBN hNA
    have hBN' : B ≤ N.map f := by
      calc B = (B.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf B).symm
        _ ≤ N.map f := Subgroup.map_mono hBN
    have hNA' : N.map f ≤ A := by
      calc N.map f ≤ (A.comap f).map f := Subgroup.map_mono hNA
        _ = A := Subgroup.map_comap_eq_self_of_surjective hf A
    rcases hmax (N.map f) (hN.map f hf) hBN' hNA' with h | h
    · left
      refine le_antisymm ?_ hBN
      calc N ≤ (N.map f).comap f := Subgroup.le_comap_map f N
        _ = B.comap f := by rw [h]
    · right
      refine le_antisymm hNA ?_
      rw [← h, Subgroup.comap_map_eq]
      exact sup_le le_rfl ((Subgroup.ker_le_comap f B).trans hBN)
  have := hG _ _ key
  rwa [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf] at this

/-- Dedekind's modular law for a normal subgroup `K`: if `B ≤ A` and `A ∩ K ≤ B`, then
`BK ∩ A = B`. -/
private theorem sup_inf_eq_of_inf_le {G : Type*} [Group G] {A B K : Subgroup G} [K.Normal]
    (hBA : B ≤ A) (hAK : A ⊓ K ≤ B) : (B ⊔ K) ⊓ A = B := by
  refine le_antisymm ?_ (le_inf le_sup_left hBA)
  intro x hx
  obtain ⟨hx, hxA⟩ := Subgroup.mem_inf.mp hx
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
  obtain ⟨b, hb, k, hk, rfl⟩ := hx
  have hkA : k ∈ A := by simpa using A.mul_mem (A.inv_mem (hBA hb)) hxA
  exact B.mul_mem hb (hAK ⟨hkA, hk⟩)

/-- If `K` is a `σ`-primary normal subgroup and `G / K` is `σ`-soluble, then `G` is `σ`-soluble:
a chief factor `A / B` either is covered by `K`, and then `|A : B|` divides `|K|`, or is
isomorphic to the chief factor `AK / BK` of `G / K`. -/
private theorem isSigmaSoluble_of_normal {I : Type} {σ : I → Set ℕ} {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] (hKp : IsSigmaPrimary σ (Nat.card K))
    (hQ : IsSigmaSoluble σ (G ⧸ K)) : IsSigmaSoluble σ G := by
  rintro A B ⟨hA, hB, hlt, hmax⟩
  have hC : ((A ⊓ K) ⊔ B).Normal := by
    have : (A ⊓ K).Normal := Subgroup.normal_inf_normal A K
    exact Subgroup.sup_normal _ _
  rcases hmax ((A ⊓ K) ⊔ B) hC le_sup_right (sup_le inf_le_left hlt.le) with h | h
  · have hAK : A ⊓ K ≤ B := by rw [← h]; exact le_sup_left
    have hmod := sup_inf_eq_of_inf_le hlt.le hAK
    set π := QuotientGroup.mk' K
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
    have hcomap : ∀ H : Subgroup G, (H.map π).comap π = H ⊔ K := fun H => by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    have key : IsChiefFactor (A.map π) (B.map π) := by
      refine ⟨hA.map π hsurj, hB.map π hsurj, lt_of_le_of_ne (Subgroup.map_mono hlt.le) ?_, ?_⟩
      · intro heq
        apply hlt.ne
        have h1 : B ⊔ K = A ⊔ K := by rw [← hcomap, ← hcomap, heq]
        rw [← hmod, h1]
        exact inf_eq_right.mpr le_sup_left
      · intro N hN hBN hNA
        have hN' : (N.comap π).Normal := hN.comap π
        have hBK : B ⊔ K ≤ N.comap π := (hcomap B).ge.trans (Subgroup.comap_mono hBN)
        have hKN : K ≤ N.comap π := le_sup_right.trans hBK
        have hNA₁ : N.comap π ≤ A ⊔ K := (Subgroup.comap_mono hNA).trans (hcomap A).le
        have : (N.comap π ⊓ A).Normal := Subgroup.normal_inf_normal _ _
        rcases hmax (N.comap π ⊓ A) this (le_inf (le_sup_left.trans hBK) hlt.le) inf_le_right
          with h' | h'
        · left
          refine le_antisymm ?_ hBN
          have hNle : N.comap π ≤ B ⊔ K := by
            intro x hx
            have hx' := hNA₁ hx
            rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx'
            obtain ⟨a, ha, k, hk, rfl⟩ := hx'
            have haN : a ∈ N.comap π := by
              simpa using (N.comap π).mul_mem hx ((N.comap π).inv_mem (hKN hk))
            have : a ∈ B := h' ▸ ⟨haN, ha⟩
            exact (B ⊔ K).mul_mem (le_sup_left (a := B) this) (le_sup_right (b := K) hk)
          calc N = (N.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hsurj N).symm
            _ ≤ (B ⊔ K).map π := Subgroup.map_mono hNle
            _ = B.map π := by
              rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff K).mpr (QuotientGroup.ker_mk' K).ge,
                sup_bot_eq]
        · right
          refine le_antisymm hNA ?_
          calc A.map π ≤ (N.comap π).map π := Subgroup.map_mono (h' ▸ inf_le_left)
            _ = N := Subgroup.map_comap_eq_self_of_surjective hsurj N
    have := hQ _ _ key
    rwa [← Subgroup.relIndex_comap, hcomap, ← Subgroup.inf_relIndex_right, hmod] at this
  · refine isSigmaPrimary_of_dvd hKp ?_
    calc B.relIndex A = B.relIndex ((A ⊓ K) ⊔ B) := by rw [h]
      _ = B.relIndex (A ⊓ K) := Subgroup.relIndex_sup_right _ _
      _ ∣ Nat.card (A ⊓ K : Subgroup G) := Subgroup.relIndex_dvd_card _ _
      _ ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right

/-- Inside every nontrivial normal subgroup `Y` of a finite `σ`-soluble group there is a
nontrivial normal `σ`-primary subgroup: a minimal normal subgroup below `Y`. -/
private theorem exists_sigmaPrimary_normal_le {I : Type} {σ : I → Set ℕ} {H : Type*} [Group H]
    [Finite H] (hH : IsSigmaSoluble σ H) {Y : Subgroup H} (hY : Y.Normal) (hY1 : Y ≠ ⊥) :
    ∃ M : Subgroup H, M.Normal ∧ M ≠ ⊥ ∧ M ≤ Y ∧ IsSigmaPrimary σ (Nat.card M) := by
  classical
  let S : Set (Subgroup H) := {M | M.Normal ∧ M ≠ ⊥ ∧ M ≤ Y}
  obtain ⟨M, hMS, hmin⟩ := S.toFinite.toFinset.exists_min_image (fun M => Nat.card M)
    ⟨Y, S.toFinite.mem_toFinset.mpr ⟨hY, hY1, le_rfl⟩⟩
  obtain ⟨hMn, hM1, hMY⟩ := S.toFinite.mem_toFinset.mp hMS
  refine ⟨M, hMn, hM1, hMY, ?_⟩
  have hchief : IsChiefFactor M ⊥ := by
    refine ⟨hMn, inferInstance, bot_lt_iff_ne_bot.mpr hM1, fun N hN _ hNM => ?_⟩
    by_cases hN1 : N = ⊥
    · exact Or.inl hN1
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hNM
        (hmin N (S.toFinite.mem_toFinset.mpr ⟨hN, hN1, hNM.trans hMY⟩)))
  simpa [Subgroup.relIndex_bot_left] using hH M ⊥ hchief

/-! ### Supplements and indices -/

/-- The hypothesis of Kourovka 19.87 for one group `G`. -/
private def SupplementHyp {I : Type} (σ : I → Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) →
    ∃ T : Subgroup G, IsSigmaSoluble σ T ∧ ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g

/-- The hypothesis of Kourovka 19.87 passes to quotients: a maximal subgroup of the image of a
Sylow subgroup `P` is the image of a maximal subgroup of `P`. -/
private theorem supplementHyp_quotient {I : Type} {σ : I → Set ℕ} {G : Type*} [Group G]
    [Finite G] (K : Subgroup G) [K.Normal] (h : SupplementHyp σ G) :
    SupplementHyp σ (G ⧸ K) := by
  intro p hp P' V' hV'
  have := Fact.mk hp
  set π := QuotientGroup.mk' K
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hsurj p P'
  rw [Sylow.coe_mapSurjective] at hV'
  set V := (P : Subgroup G) ⊓ V'.comap π
  have hle : V' ≤ (P : Subgroup G).map π := hV'.lt.le
  have hmapV : V.map π = V' := by
    refine le_antisymm ((Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hle hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hV : V ⋖ (P : Subgroup G) := by
    refine ⟨lt_of_le_of_ne inf_le_left fun hVP => hV'.lt.ne ?_, fun W hVW hWP => ?_⟩
    · rw [← hmapV, hVP]
    rcases hV'.eq_or_eq (hmapV ▸ Subgroup.map_mono hVW.le) (Subgroup.map_mono hWP.le) with h | h
    · exact hVW.not_ge (le_inf hWP.le (Subgroup.map_le_iff_le_comap.mp h.le))
    · refine hWP.not_ge fun x hx => ?_
      obtain ⟨w, hw, hwx⟩ : π x ∈ W.map π := h ▸ Subgroup.mem_map_of_mem π hx
      have hk : w⁻¹ * x ∈ V := by
        refine ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem (hWP.le hw)) hx, ?_⟩
        change π (w⁻¹ * x) ∈ V'
        rw [map_mul, map_inv, hwx, inv_mul_cancel]
        exact V'.one_mem
      simpa using W.mul_mem hw (hVW.le hk)
  obtain ⟨T, hT, hVT⟩ := h p hp P V hV
  refine ⟨T.map π, isSigmaSoluble_of_surjective (π.subgroupMap_surjective T) hT, fun g' => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj g'
  obtain ⟨v, hv, t, ht, rfl⟩ := hVT g
  exact ⟨π v, hv.2, π t, Subgroup.mem_map_of_mem π ht, (map_mul π v t).symm⟩

/-- If `V T = G`, then `|V : V ∩ T| = |G : T|`. -/
private theorem relIndex_eq_index_of_forall_mul {G : Type*} [Group G] {V T : Subgroup G}
    (h : ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g) : T.relIndex V = T.index := by
  have horbit : MulAction.orbit V ((1 : G) : G ⧸ T) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v, hv, t, ht, rfl⟩ := h g
    refine ⟨⟨v, hv⟩, ?_⟩
    change (⟨v, hv⟩ : V) • ((1 : G) : G ⧸ T) = ((v * t : G) : G ⧸ T)
    rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simpa using ht
  have hstab : MulAction.stabilizer V ((1 : G) : G ⧸ T) = T.subgroupOf V := by
    rw [← MulAction.stabilizer_subgroupOf, MulAction.stabilizer_quotient]
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horbit, Set.ncard_univ,
    Subgroup.index_eq_card]

/-- Conversely, if `|V : V ∩ T| = |G : T|` in a finite group, then `V T = G`. -/
private theorem forall_mul_of_relIndex_eq_index {G : Type*} [Group G] [Finite G]
    {V T : Subgroup G} (h : T.relIndex V = T.index) (g : G) : ∃ v ∈ V, ∃ t ∈ T, v * t = g := by
  have hstab : MulAction.stabilizer V ((1 : G) : G ⧸ T) = T.subgroupOf V := by
    rw [← MulAction.stabilizer_subgroupOf, MulAction.stabilizer_quotient]
  have hcard : (MulAction.orbit V ((1 : G) : G ⧸ T)).ncard = Nat.card (G ⧸ T) := by
    rw [← MulAction.index_stabilizer, hstab, ← Subgroup.relIndex, h, Subgroup.index_eq_card]
  have horbit : MulAction.orbit V ((1 : G) : G ⧸ T) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ, hcard])
  obtain ⟨⟨v, hv⟩, hvg⟩ : ((g : G) : G ⧸ T) ∈ MulAction.orbit V ((1 : G) : G ⧸ T) :=
    horbit ▸ Set.mem_univ _
  change (⟨v, hv⟩ : V) • ((1 : G) : G ⧸ T) = ((g : G) : G ⧸ T) at hvg
  rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at hvg
  exact ⟨v, hv, v⁻¹ * g, hvg, mul_inv_cancel_left v g⟩

/-- Subgroups `T₁, T₂` of coprime indices in a finite group satisfy `|T₁ : T₁ ∩ T₂| = |G : T₂|`. -/
private theorem relIndex_eq_index_of_coprime {G : Type*} [Group G] [Finite G]
    {T₁ T₂ : Subgroup G} (hcop : Nat.Coprime T₁.index T₂.index) :
    T₂.relIndex T₁ = T₂.index := by
  have hdvd : T₂.index ∣ T₂.relIndex T₁ * T₁.index := by
    rw [← Subgroup.index_inf, inf_comm, Subgroup.index_inf]
    exact dvd_mul_left _ _
  have hdvd' : T₂.index ∣ T₂.relIndex T₁ := hcop.symm.dvd_of_dvd_mul_right hdvd
  have hle : T₂.relIndex T₁ ≤ T₂.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  exact le_antisymm hle (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd')

/-- If every element of `L` is a product `x y` with `x ∈ H ≤ L` and `y ∈ K`, then
`|H : H ∩ K| = |L : L ∩ K|`. -/
private theorem relIndex_eq_of_forall_mul {G : Type*} [Group G] {H K L : Subgroup G}
    (hHL : H ≤ L) (h : ∀ l ∈ L, ∃ x ∈ H, ∃ y ∈ K, x * y = l) : K.relIndex H = K.relIndex L := by
  rw [← Subgroup.relIndex_subgroupOf hHL]
  refine relIndex_eq_index_of_forall_mul fun l => ?_
  obtain ⟨x, hx, y, hy, hxy⟩ := h l l.2
  have hyL : y ∈ L := by
    rw [show y = x⁻¹ * l by rw [← hxy, inv_mul_cancel_left]]
    exact L.mul_mem (L.inv_mem (hHL hx)) l.2
  exact ⟨⟨x, hHL hx⟩, hx, ⟨y, hyL⟩, hy, Subtype.ext hxy⟩

/-- The supplement of a maximal subgroup of a Sylow `q`-subgroup has `q`-power index. -/
private theorem exists_supplement {I : Type} {σ : I → Set ℕ} {G : Type*} [Group G] [Finite G]
    (hyp : SupplementHyp σ G) {q : ℕ} (hq : q.Prime) (hqG : q ∣ Nat.card G) :
    ∃ T : Subgroup G, IsSigmaSoluble σ T ∧ ∃ a, T.index = q ^ a := by
  have := Fact.mk hq
  obtain ⟨P⟩ : Nonempty (Sylow q G) := inferInstance
  obtain ⟨V, -, hV⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr (P.ne_bot_of_dvd_card hqG))
  obtain ⟨T, hT, hVT⟩ := hyp q hq P V hV
  refine ⟨T, hT, ?_⟩
  have hdvd : T.index ∣ q ^ (Nat.card G).factorization q := by
    rw [← relIndex_eq_index_of_forall_mul hVT, ← P.card_eq_multiplicity]
    exact (Subgroup.relIndex_dvd_card T V).trans (Subgroup.card_dvd_of_le hV.le)
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  exact ⟨a, ha⟩

/-! ### Normal `σ`-primary subgroups -/

/-- A subgroup `T` normalizes the image in `G` of every normal subgroup of `T`. -/
private theorem le_normalizer_map_subtype {G : Type*} [Group G] {T : Subgroup G}
    {R : Subgroup T} (hR : R.Normal) :
    T ≤ Subgroup.normalizer ((R.map T.subtype : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  set x' : T := ⟨x, hx⟩
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨x' * m * x'⁻¹, hR.conj_mem m hm x', rfl⟩
  · rintro ⟨m, hm, hmy⟩
    refine ⟨x'⁻¹ * m * x', by simpa using hR.conj_mem m hm x'⁻¹, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hmy ⊢
    rw [hmy]
    simp [x', mul_assoc]

/-- If `X` is normal and `M ≤ X` is a nontrivial `S`-subgroup normalized by `X` (all prime
divisors of `|M|` lie in `S`), then `G` has a nontrivial normal `S`-subgroup: an `S`-subgroup of
largest order among those normalized by `X` and contained in `X`. -/
private theorem exists_normal_of_le_normalizer {G : Type*} [Group G] [Finite G] (S : Set ℕ)
    {X M : Subgroup G} (hX : X.Normal) (hMX : M ≤ X)
    (hXM : X ≤ Subgroup.normalizer (M : Set G)) (hM : M ≠ ⊥)
    (hMS : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p ∈ S) :
    ∃ K : Subgroup G, K.Normal ∧ K ≠ ⊥ ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p ∈ S := by
  classical
  let 𝒮 : Set (Subgroup G) := {K | K ≤ X ∧ X ≤ Subgroup.normalizer (K : Set G) ∧
    ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p ∈ S}
  obtain ⟨K, hK𝒮, hmax⟩ := 𝒮.toFinite.toFinset.exists_max_image (fun K => Nat.card K)
    ⟨M, 𝒮.toFinite.mem_toFinset.mpr ⟨hMX, hXM, hMS⟩⟩
  obtain ⟨hKX, hXK, hKS⟩ := 𝒮.toFinite.mem_toFinset.mp hK𝒮
  -- The join of `K` with a member of `𝒮` is in `𝒮`.
  have hjoin : ∀ K' ∈ 𝒮, K ⊔ K' ∈ 𝒮 := by
    rintro K' ⟨hK'X, hXK', hK'S⟩
    refine ⟨sup_le hKX hK'X,
      (le_inf hXK hXK').trans (Subgroup.inf_normalizer_le_normalizer_sup K K'), fun p hp hpd => ?_⟩
    have hcard : Nat.card (K ⊔ K' : Subgroup G) = K.relIndex K' * Nat.card K := by
      have h1 : K.relIndex (K ⊔ K') = K.relIndex K' := by
        refine (relIndex_eq_of_forall_mul le_sup_right fun l hl => ?_).symm
        have hl' : l ∈ ((K' ⊔ K : Subgroup G) : Set G) := by rw [sup_comm]; exact hl
        rw [Subgroup.coe_mul_of_left_le_normalizer_right K' K (hK'X.trans hXK)] at hl'
        obtain ⟨x, hx, y, hy, rfl⟩ := hl'
        exact ⟨x, hx, y, hy, rfl⟩
      rw [← h1, ← Subgroup.relIndex_mul_card K (K ⊔ K'), inf_sup_self]
    rw [hcard] at hpd
    rcases hp.dvd_mul.mp hpd with h | h
    · exact hK'S p hp (h.trans (Subgroup.relIndex_dvd_card K K'))
    · exact hKS p hp h
  -- Every conjugate of `K` is in `𝒮`, so it lies in `K` by maximality.
  have hconj : ∀ g : G, K.map (MulAut.conj g).toMonoidHom ≤ K := by
    intro g
    set K' := K.map (MulAut.conj g).toMonoidHom
    have hmem : ∀ y, y ∈ K' ↔ g⁻¹ * y * g ∈ K := fun y => by
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro h
        exact ⟨g⁻¹ * y * g, h, by simp [mul_assoc]⟩
    have hK' : K' ∈ 𝒮 := by
      refine ⟨fun y hy => ?_, fun x hx => ?_, ?_⟩
      · have := (hmem y).mp hy
        simpa [mul_assoc] using hX.conj_mem _ (hKX this) g
      · rw [Subgroup.mem_normalizer_iff]
        intro y
        have hx' : g⁻¹ * x * g ∈ X := by simpa using hX.conj_mem x hx g⁻¹
        rw [hmem, hmem, Subgroup.mem_normalizer_iff.mp (hXK hx') (g⁻¹ * y * g)]
        constructor <;> intro h <;> convert h using 1 <;> group
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact hKS
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : K ≤ K ⊔ K')
      (hmax _ (𝒮.toFinite.mem_toFinset.mpr (hjoin K' hK')))
    exact heq ▸ le_sup_right
  refine ⟨K, ⟨fun n hn g => hconj g ⟨n, hn, rfl⟩⟩, fun hK1 => hM ?_, hKS⟩
  have h1 := hmax M (𝒮.toFinite.mem_toFinset.mpr ⟨hMX, hXM, hMS⟩)
  rw [hK1, Subgroup.card_bot] at h1
  exact M.eq_bot_of_card_le h1

/-- The key step (claim (**) of Liu, Guo, Safonova and Skiba): let `T₁` and `T₂` be subgroups of
coprime indices, `|G : T₂|` a power of the prime `q`, `T₂` `σ`-soluble, and let `R ≤ T₁` be a
nontrivial subgroup normalized by `T₁` whose order is prime to `q`. Then `R` lies in the normal
core of `T₂`, and `G` has a nontrivial normal `σ`-primary subgroup. -/
private theorem exists_normal_of_supplements {I : Type} {σ : I → Set ℕ} {G : Type*} [Group G]
    [Finite G] {T₁ T₂ R : Subgroup G} {q b : ℕ} (hq : q.Prime)
    (hcop : Nat.Coprime T₁.index T₂.index) (hT₂ : T₂.index = q ^ b) (hRT₁ : R ≤ T₁)
    (hT₁R : T₁ ≤ Subgroup.normalizer (R : Set G)) (hR : R ≠ ⊥) (hRq : ¬ q ∣ Nat.card R)
    (hsol : IsSigmaSoluble σ T₂) :
    ∃ K : Subgroup G, K.Normal ∧ K ≠ ⊥ ∧ IsSigmaPrimary σ (Nat.card K) := by
  -- `R ≤ T₂`: the index `|R : R ∩ T₂|` divides both `|R|` and `|T₁ : T₁ ∩ T₂| = q ^ b`.
  have hRT₂ : R ≤ T₂ := by
    have hWT₁ : R ⊔ (T₁ ⊓ T₂) ≤ T₁ := sup_le hRT₁ inf_le_left
    have h1 : (T₁ ⊓ T₂).relIndex (R ⊔ (T₁ ⊓ T₂)) ∣ q ^ b := by
      have e1 : (T₁ ⊓ T₂).relIndex T₁ = q ^ b := by
        rw [Subgroup.inf_relIndex_left, relIndex_eq_index_of_coprime hcop, hT₂]
      rw [← e1, ← Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hWT₁]
      exact dvd_mul_right _ _
    have h2 : (T₁ ⊓ T₂).relIndex (R ⊔ (T₁ ⊓ T₂)) = (T₁ ⊓ T₂).relIndex R := by
      refine (relIndex_eq_of_forall_mul le_sup_left fun l hl => ?_).symm
      rw [← SetLike.mem_coe,
        Subgroup.coe_mul_of_right_le_normalizer_left R _ (inf_le_left.trans hT₁R)] at hl
      obtain ⟨x, hx, y, hy, rfl⟩ := hl
      exact ⟨x, hx, y, hy, rfl⟩
    have hcop' : Nat.Coprime ((T₁ ⊓ T₂).relIndex R) (Nat.card R) :=
      Nat.Coprime.coprime_dvd_left (h2 ▸ h1)
        (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hq).mpr hRq))
    have h4 : (T₁ ⊓ T₂).relIndex R = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop' (Subgroup.relIndex_dvd_card _ _)
    exact (Subgroup.relIndex_eq_one.mp h4).trans inf_le_right
  -- `G = T₂ T₁`, so every conjugate of `R` lies in `T₂`.
  have hprod : ∀ g : G, ∃ x ∈ T₂, ∃ y ∈ T₁, x * y = g :=
    forall_mul_of_relIndex_eq_index (relIndex_eq_index_of_coprime hcop.symm)
  have hRX : R ≤ T₂.normalCore := by
    intro r hr
    change ∀ g : G, g * r * g⁻¹ ∈ T₂
    intro g
    obtain ⟨x, hx, y, hy, rfl⟩ := hprod g
    have hyr : y * r * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hT₁R hy) r).mp hr
    have := T₂.mul_mem (T₂.mul_mem hx (hRT₂ hyr)) (T₂.inv_mem hx)
    simpa [mul_assoc] using this
  -- The normal core `X` of `T₂` is nontrivial and normal in the `σ`-soluble group `T₂`.
  set X := T₂.normalCore
  have hXT₂ : X ≤ T₂ := Subgroup.normalCore_le T₂
  have hX1 : X ≠ ⊥ := fun h => hR (le_bot_iff.mp (h ▸ hRX))
  have hY1 : X.subgroupOf T₂ ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hdisj => hX1 (hdisj.eq_bot_of_le hXT₂)
  obtain ⟨M, hMn, hM1, hMY, i, hMi⟩ :=
    exists_sigmaPrimary_normal_le hsol ((Subgroup.normalCore_normal T₂).subgroupOf T₂) hY1
  have hM₀X : M.map T₂.subtype ≤ X :=
    (Subgroup.map_mono hMY).trans (Subgroup.map_subgroupOf_eq_of_le hXT₂).le
  have hM₀1 : M.map T₂.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ T₂.subtype_injective]
  have hcard : Nat.card (M.map T₂.subtype) = Nat.card M :=
    Subgroup.card_map_of_injective T₂.subtype_injective
  obtain ⟨K, hK, hK1, hKi⟩ := exists_normal_of_le_normalizer (σ i)
    (Subgroup.normalCore_normal T₂) hM₀X (hXT₂.trans (le_normalizer_map_subtype hMn)) hM₀1
    (by rw [hcard]; exact hMi)
  exact ⟨K, hK, hK1, i, hKi⟩

/-! ### Solvable groups -/

/-- A nontrivial finite solvable group has a nontrivial normal subgroup of prime power order: the
elements of `p`-power order in the last nontrivial term of the derived series. -/
private theorem exists_normal_prime_pow_of_isSolvable {G : Type*} [Group G] [Finite G]
    [Nontrivial G] (hG : Group.IsSolvable G) :
    ∃ (p : ℕ) (K : Subgroup G), p.Prime ∧ K.Normal ∧ K ≠ ⊥ ∧ ∃ n, Nat.card K = p ^ n := by
  classical
  have hex : ∃ n, Subgroup.derivedSeries G n = ⊥ := (Group.isSolvable_def G).mp hG
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, Subgroup.derivedSeries_zero] at this
    exact top_ne_bot this
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  set D := Subgroup.derivedSeries G k
  have hD1 : D ≠ ⊥ := Nat.find_min hex (by omega : k < Nat.find hex)
  have hDD : ⁅D, D⁆ = ⊥ := by
    rw [← Subgroup.derivedSeries_succ, ← hk]
    exact Nat.find_spec hex
  have hDn : D.Normal := Subgroup.derivedSeries_normal G k
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, Commute x y := by
    intro x hx y hy
    have := Subgroup.commutator_mem_commutator hx hy
    rw [hDD, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd fun h => hD1 (Subgroup.card_eq_one.mp h)
  have := Fact.mk hp
  let K : Subgroup G :=
    { carrier := {x | x ∈ D ∧ x ^ p ^ Nat.card G = 1}
      mul_mem' := fun {a b} ha hb => ⟨D.mul_mem ha.1 hb.1, by
        rw [(hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨D.one_mem, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨D.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  refine ⟨p, K, hp, ⟨fun n hn g => ⟨hDn.conj_mem n hn.1 g, ?_⟩⟩, fun hK => ?_, ?_⟩
  · rw [conj_pow, hn.2, mul_one, mul_inv_cancel]
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) p hpD
    have hxK : (x : G) ∈ K := by
      refine ⟨x.2, ?_⟩
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hx]
      exact dvd_pow_self p Nat.card_pos.ne'
    rw [hK, Subgroup.mem_bot] at hxK
    have hx1 : x = 1 := Subtype.ext hxK
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  · refine IsPGroup.iff_card.mp fun x => ⟨Nat.card G, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact x.2.2

/-- A finite group whose order has no prime divisors other than `q` and `q'` is solvable, by
Burnside's `p^a q^b` theorem. -/
private theorem isSolvable_of_two_primes {G : Type*} [Group G] [Finite G] {q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hne : q ≠ q')
    (h : ∀ r, r.Prime → r ∣ Nat.card G → r = q ∨ r = q') : Group.IsSolvable G := by
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hsub : (Nat.card G).factorization.support ⊆ {q, q'} := by
    intro r hr
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hr
    rcases h r hr.1 hr.2.1 with rfl | rfl <;> simp
  have hcard : Nat.card G =
      q ^ (Nat.card G).factorization q * q' ^ (Nat.card G).factorization q' := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _), Finset.prod_pair hne]
  have := Fintype.ofFinite G
  exact BurnsidePaqb.burnside_paqb q q' _ _ hq hq'
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)

/-! ### The theorem -/

/--
**σ-soluble supplements to the maximal subgroups of Sylow subgroups (Kourovka 19.87).** Let $\sigma$
be a partition of the set of all primes and let $G$ be a finite group. If for every prime $p$, every
Sylow $p$-subgroup $P$ of $G$ and every maximal subgroup $V$ of $P$ there is a $\sigma$-soluble
subgroup $T$ of $G$ with $VT = G$, that is, every element of $G$ is a product $vt$ with $v \in V$
and $t \in T$, then $G$ is $\sigma$-soluble. Here a partition of the primes is a family of nonempty,
pairwise disjoint sets of primes whose union is the set of all primes, and a group is
$\sigma$-soluble when for every chief factor $A/B$ of it (normal subgroups $B < A$ with no normal
subgroup strictly between them) all prime divisors of the index $|A : B|$ lie in a single block of
$\sigma$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.87 (A. N.
Skiba); resolution: A.-M. Liu, W. Guo, I. N. Safonova and A. N. Skiba, G-covering subgroup systems
for some classes of σ-soluble groups, J. Algebra 585 (2021), 280-293; another solution using CFSG by
S. F. Kamornikov and V. N. Tyutyanov, Trudy Inst. Mat. Mekh. UrO RAN 27 (2021), no. 1, 98-102,
abstract: a set of subgroups of G containing a supplement to each maximal subgroup of every Sylow
subgroup of G is a G-covering subgroup system for the classes of σ-soluble and of σ-nilpotent
groups, which answers 19.87 and 19.88; Kourovka Archive, Problem 19.87: Yes, it is true,
https://doi.org/10.1016/j.jalgebra.2021.06.010.
-/
theorem sylowMaximalSigmaSolubleSupplement_holds : sylowMaximalSigmaSolubleSupplement := by
  intro I σ hσ
  suffices ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n → SupplementHyp σ G →
      IsSigmaSoluble σ G from fun G _ _ hyp => this _ G rfl hyp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hyp
  by_contra hG
  -- `G` has no nontrivial normal σ-primary subgroup, by induction on `G / K` (claim (*)).
  have h0 : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → ¬ IsSigmaPrimary σ (Nat.card K) := by
    intro K hK hK1 hKp
    have hlt : Nat.card (G ⧸ K) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup K]
      exact lt_mul_of_one_lt_right Nat.card_pos ((Subgroup.one_lt_card_iff_ne_bot K).mpr hK1)
    exact hG (isSigmaSoluble_of_normal K hKp
      (ih _ hlt (G ⧸ K) rfl (supplementHyp_quotient K hyp)))
  -- `G` is not σ-primary.
  have hnp : ¬ IsSigmaPrimary σ (Nat.card G) := fun h => hG (isSigmaSoluble_of_isSigmaPrimary h)
  -- For every prime `q ∣ |G|` some block contains every other prime divisor of `|G|`, but not `q`.
  have hkey : ∀ q, q.Prime → q ∣ Nat.card G →
      ∃ k, q ∉ σ k ∧ ∀ r, r.Prime → r ∣ Nat.card G → r ≠ q → r ∈ σ k := by
    intro q hq hqG
    obtain ⟨T, hT, a, ha⟩ := exists_supplement hyp hq hqG
    have hT1 : T ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.index_bot] at ha
      exact hnp (ha ▸ isSigmaPrimary_prime_pow hσ hq)
    have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
    obtain ⟨R, hRn, hR1, -, k, hRk⟩ :=
      exists_sigmaPrimary_normal_le hT (Y := ⊤) inferInstance top_ne_bot
    have hR₀1 : R.map T.subtype ≠ ⊥ := by
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective]
    have hcard : Nat.card (R.map T.subtype) = Nat.card R :=
      Subgroup.card_map_of_injective T.subtype_injective
    have hother : ∀ r, r.Prime → r ∣ Nat.card G → r ≠ q → r ∈ σ k := by
      intro r hr hrG hrq
      by_contra hrk
      obtain ⟨T₂, hT₂, b, hb⟩ := exists_supplement hyp hr hrG
      have hcop : Nat.Coprime T.index T₂.index := by
        rw [ha, hb]
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hr).mpr (Ne.symm hrq))
      obtain ⟨K, hK, hK1, hKp⟩ := exists_normal_of_supplements hr hcop hb
        (Subgroup.map_subtype_le R) (le_normalizer_map_subtype hRn) hR₀1
        (fun h => hrk (hRk r hr (hcard ▸ h))) hT₂
      exact h0 K hK hK1 hKp
    refine ⟨k, fun hqk => hnp ⟨k, fun r hr hrG => ?_⟩, hother⟩
    by_cases hrq : r = q
    · exact hrq ▸ hqk
    · exact hother r hr hrG hrq
  -- Two distinct primes divide `|G|`.
  obtain ⟨q, hq, hqG⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card G := by
    refine Nat.exists_prime_and_dvd fun h1 => hnp ?_
    obtain ⟨i, -⟩ := hσ.2.2 2 Nat.prime_two
    exact ⟨i, fun p hp hp1 => absurd (Nat.le_of_dvd one_pos (h1 ▸ hp1)) hp.one_lt.not_ge⟩
  obtain ⟨k, hqk, hk⟩ := hkey q hq hqG
  obtain ⟨q', hq', hq'G, hne⟩ : ∃ q', q'.Prime ∧ q' ∣ Nat.card G ∧ q' ≠ q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := hσ.2.2 q hq
    exact hnp ⟨i, fun r hr hrG => hcon r hr hrG ▸ hi⟩
  obtain ⟨k', hq'k', hk'⟩ := hkey q' hq' hq'G
  have hkk' : k ≠ k' := by
    rintro rfl
    exact hq'k' (hk q' hq' hq'G hne)
  -- Hence `|G|` has only the prime divisors `q` and `q'`, and `G` is solvable by Burnside.
  have hall : ∀ r, r.Prime → r ∣ Nat.card G → r = q ∨ r = q' := by
    intro r hr hrG
    by_contra hcon
    push Not at hcon
    exact Set.disjoint_left.mp (hσ.2.1 k k' hkk') (hk r hr hrG hcon.1) (hk' r hr hrG hcon.2)
  have hsolv := isSolvable_of_two_primes hq hq' hne.symm hall
  have : Nontrivial G :=
    Finite.one_lt_card_iff_nontrivial.mp (hq.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hqG))
  obtain ⟨p, K, hp, hK, hK1, m, hm⟩ := exists_normal_prime_pow_of_isSolvable hsolv
  exact h0 K hK hK1 (hm ▸ isSigmaPrimary_prime_pow hσ hp)

end MathlibExt.GroupTheory.SylowMaximalSigmaSolubleSupplementKourovka19Problem87Wanted
