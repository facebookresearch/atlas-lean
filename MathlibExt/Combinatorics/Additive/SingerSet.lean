/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Ring

/-!
# Affine equivalences between Singer sets

`zModAffinelyEquivalent_singerSet` proves four sufficient conditions for two generalized
Singer sets to be affinely equivalent.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Singer set.** Let $F$ be a finite field with $q$ elements, let $K$ be a field
extension of $F$, let $\theta \in K$, let $h$ and $b$ be natural numbers, and put
$M = (q^{h+1} - 1)/(q - 1)$. The generalized Singer set $\mathrm{Singer}_h(q, b)$ is the set of
residues $a \in \mathbb{Z}/M\mathbb{Z}$ such that $\theta^a = u\theta^b + v$ for some
$u, v \in F$, where $\theta^a$ means $\theta$ raised to the least nonnegative representative
of $a$.

The construction is intended for $[K : F] = h + 1$ and $\theta$ a generator of $K^\times$; the
definition itself does not assume either.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 2. -/
public def singerSet (F : Type*) {K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) :
    Set (ZMod ((Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1))) :=
  {a | ∃ u v : F, θ ^ a.val = algebraMap F K u * θ ^ b + algebraMap F K v}

/-- **Membership in a Singer set.** Let $F$ be a finite field with $q$ elements, let $K$ be a
field extension of $F$, let $\theta \in K$, let $h$ and $b$ be natural numbers, and put
$M = (q^{h+1} - 1)/(q - 1)$. A residue $a \in \mathbb{Z}/M\mathbb{Z}$ lies in the Singer set
$\mathrm{Singer}_h(q, b)$ built from $F$, $K$ and $\theta$ if and only if
$\theta^a = u\theta^b + v$ for some $u, v \in F$, where $\theta^a$ means $\theta$ raised to the
least nonnegative representative of $a$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 2. -/
public theorem mem_singerSet {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ)
    (a : ZMod ((Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1))) :
    a ∈ singerSet F h θ b ↔
      ∃ u v : F, θ ^ a.val = algebraMap F K u * θ ^ b + algebraMap F K v :=
  Iff.rfl

/-- **Affine equivalence of sets of residues.** For a natural number $M$, sets
$A_1, A_2 \subseteq \mathbb{Z}/M\mathbb{Z}$ are affinely equivalent, written $A_1 \sim A_2$, if
there are a unit $d$ of $\mathbb{Z}/M\mathbb{Z}$ and an element $s \in \mathbb{Z}/M\mathbb{Z}$
such that $A_2 = \{d a + s : a \in A_1\}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition before Theorem 4. -/
public def ZModAffinelyEquivalent {M : ℕ} (A₁ A₂ : Set (ZMod M)) : Prop :=
  ∃ d s : ZMod M, IsUnit d ∧ A₂ = (fun a => d * a + s) '' A₁

/-- **Affine equivalence is reflexive.** For every natural number $M$, every subset $A$ of
$\mathbb{Z}/M\mathbb{Z}$ is affinely equivalent to itself (take $d = 1$ and $s = 0$).

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition before Theorem 4. -/
public theorem zModAffinelyEquivalent_refl {M : ℕ} (A : Set (ZMod M)) :
    ZModAffinelyEquivalent A A :=
  ⟨1, 0, isUnit_one, by simp⟩

namespace zModAffinelyEquivalent_singerSet

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private abbrev plane (F : Type*) [Field F] [Algebra F K] (x : K) : Submodule F K :=
  Submodule.span F ({1, x} : Set K)

private theorem mem_plane {x z : K} :
    z ∈ plane F x ↔ ∃ u v : F, z = algebraMap F K u * x + algebraMap F K v := by
  rw [Submodule.mem_span_pair]
  constructor <;> rintro ⟨u, v, huv⟩ <;>
    exact ⟨v, u, by simpa [Algebra.smul_def, add_comm] using huv.symm⟩

private theorem independent_of_notMem {x : K} (hx : x ∉ (algebraMap F K).range) :
    LinearIndependent F ![1, x] :=
  (LinearIndependent.pair_iff' one_ne_zero).2 fun a ha =>
    hx ⟨a, by simpa [Algebra.smul_def] using ha⟩

private theorem finrank_plane {x : K} (hx : x ∉ (algebraMap F K).range) :
    Module.finrank F (plane F x) = 2 := by
  rw [plane, ← Matrix.range_cons_cons_empty 1 x ![],
    finrank_span_eq_card (independent_of_notMem hx), Fintype.card_fin]

/-- Multiplication by `c` carries the entire first plane onto the second once it
carries each generator into the second plane. -/
private theorem mul_mem_plane_iff [Finite K] {x y c z : K}
    (hx : x ∉ (algebraMap F K).range) (hy : y ∉ (algebraMap F K).range)
    (hc : c ≠ 0) (hc₁ : c ∈ plane F y) (hcx : c * x ∈ plane F y) :
    c * z ∈ plane F y ↔ z ∈ plane F x := by
  let f := Units.mulLeftLinearEquiv F K (Units.mk0 c hc)
  have hmap : (plane F x).map f.toLinearMap = plane F y := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      simpa [f, Set.insert_subset_iff, Submodule.mem_comap] using And.intro hc₁ hcx
    · rw [f.finrank_map_eq, finrank_plane hx, finrank_plane hy]
  change f z ∈ plane F y ↔ _
  rw [← hmap, Submodule.mem_map_equiv, f.symm_apply_apply]

private theorem frobenius_mem_plane_iff [Finite F] [Finite K] {p : ℕ} [ExpChar F p] [ExpChar K p]
    (i : ℕ) (x z : K) : z ^ p ^ i ∈ plane F (x ^ p ^ i) ↔ z ∈ plane F x := by
  rw [mem_plane, mem_plane]
  constructor
  · rintro ⟨u, v, huv⟩
    obtain ⟨a, rfl⟩ := (iterateFrobeniusEquiv F p i).surjective u
    obtain ⟨b, rfl⟩ := (iterateFrobeniusEquiv F p i).surjective v
    refine ⟨a, b, (iterateFrobeniusEquiv K p i).injective ?_⟩
    simpa only [iterateFrobeniusEquiv_def, add_pow_expChar_pow, mul_pow, map_pow] using huv
  · rintro ⟨u, v, rfl⟩
    exact ⟨u ^ p ^ i, v ^ p ^ i, by rw [add_pow_expChar_pow, mul_pow, map_pow, map_pow]⟩

variable [Fintype F] {h : ℕ} {θ : K}

local notation "M" => (Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1)

/-- Reducing the exponent modulo the Singer modulus removes a nonzero power of the norm. -/
private theorem pow_mem_mod_iff [Finite K] (hK : Module.finrank F K = h + 1) (hθ₀ : θ ≠ 0)
    (P : Submodule F K) (a : ℕ) : θ ^ (a % M) ∈ P ↔ θ ^ a ∈ P := by
  have hnorm : algebraMap F K (Algebra.norm F θ) = θ ^ M := by
    rw [FiniteField.algebraMap_norm_eq_pow, Module.natCard_eq_pow_finrank (K := F) (V := K),
      hK, Nat.card_eq_fintype_card]
  have hpow : θ ^ a = (Algebra.norm F θ ^ (a / M)) • θ ^ (a % M) := by
    rw [Algebra.smul_def, map_pow, hnorm, ← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hpow, P.smul_mem_iff (pow_ne_zero _ (Algebra.norm_ne_zero_iff.mpr hθ₀))]

private theorem natCast_mem_singerSet [Finite K] (hK : Module.finrank F K = h + 1) (hθ₀ : θ ≠ 0)
    (a b : ℕ) : (a : ZMod M) ∈ singerSet F h θ b ↔ θ ^ a ∈ plane F (θ ^ b) := by
  rw [mem_singerSet, ZMod.val_natCast, ← mem_plane, pow_mem_mod_iff hK hθ₀]

private theorem exists_pow_of_order [Fintype K] {c : K} (hc : c ≠ 0) (hθ₀ : θ ≠ 0)
    (hθ : orderOf θ = Fintype.card K - 1) : ∃ k : ℕ, θ ^ k = c := by
  classical
  let g := Units.mk0 θ hθ₀
  have hg : Subgroup.zpowers g = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top _).mp
    rw [Nat.card_zpowers, ← orderOf_units, Nat.card_eq_fintype_card, Fintype.card_units]
    exact hθ
  have hmem : Units.mk0 c hc ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers, hg]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, congrArg Units.val hk⟩

private theorem affine_of_shift [Finite K] [NeZero M] (hK : Module.finrank F K = h + 1)
    (hθ₀ : θ ≠ 0) {b e k : ℕ} (hb : θ ^ b ∉ (algebraMap F K).range)
    (he : θ ^ e ∉ (algebraMap F K).range) (hk : θ ^ k ∈ plane F (θ ^ e))
    (hkb : θ ^ k * θ ^ b ∈ plane F (θ ^ e)) :
    ZModAffinelyEquivalent (singerSet F h θ b) (singerSet F h θ e) := by
  have hmem (a : ZMod M) : a + k ∈ singerSet F h θ e ↔ a ∈ singerSet F h θ b := by
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
    rw [← Nat.cast_add, natCast_mem_singerSet hK hθ₀, natCast_mem_singerSet hK hθ₀,
      add_comm, pow_add, mul_mem_plane_iff hb he (pow_ne_zero k hθ₀) hk hkb]
  refine ⟨1, k, isUnit_one, ?_⟩
  simp only [one_mul]
  ext a
  exact ⟨fun ha => ⟨a - k, (hmem _).mp (by simpa), sub_add_cancel _ _⟩,
    fun ⟨n, hn, hna⟩ => hna ▸ (hmem n).mpr hn⟩

private theorem affine_of_frobenius [Finite K] [NeZero M] (hK : Module.finrank F K = h + 1)
    (hθ₀ : θ ≠ 0) {b e i : ℕ} (hb : θ ^ b = (θ ^ e) ^ ringChar F ^ i) :
    ZModAffinelyEquivalent (singerSet F h θ b) (singerSet F h θ e) := by
  let p := ringChar F
  obtain ⟨n, hp, hq⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_injective_algebraMap' F p
  have hdvd : p ∣ Fintype.card F ^ (h + 1) := by
    rw [hq, ← pow_mul]
    exact dvd_pow_self _ (by positivity)
  have hcop : p.Coprime M := by
    apply Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd (Nat.sub_one_dvd_pow_sub_one _ _))
    apply Nat.Coprime.of_dvd_left hdvd
    exact (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ Fintype.card_pos)).mpr
      (Nat.coprime_one_right _)
  obtain ⟨d, hd⟩ := (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_left i)
  have hmem (a : ZMod M) : (d : ZMod M) * a ∈ singerSet F h θ b ↔
      a ∈ singerSet F h θ e := by
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
    rw [hd, ← Nat.cast_mul, natCast_mem_singerSet hK hθ₀, natCast_mem_singerSet hK hθ₀,
      mul_comm, pow_mul, hb, frobenius_mem_plane_iff (p := p)]
  refine ⟨↑d⁻¹, 0, d⁻¹.isUnit, ?_⟩
  simp only [add_zero]
  ext a
  constructor
  · intro ha
    exact ⟨d * a, (hmem a).mpr ha, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact (hmem _).mp (by simpa)

private theorem affine_of_relation [Fintype K] [NeZero M] (hK : Module.finrank F K = h + 1)
    (hθ₀ : θ ≠ 0) (hθ : orderOf θ = Fintype.card K - 1) {b e : ℕ}
    (hb : θ ^ b ∉ (algebraMap F K).range) (he : θ ^ e ∉ (algebraMap F K).range)
    {r t w s : F} (hrt : r ≠ 0 ∨ t ≠ 0)
    (hs : algebraMap F K s = algebraMap F K r * θ ^ b + algebraMap F K t * θ ^ (e + b) +
      algebraMap F K w * θ ^ e) :
    ZModAffinelyEquivalent (singerSet F h θ b) (singerSet F h θ e) := by
  let c := algebraMap F K r + algebraMap F K t * θ ^ e
  have hc : c ≠ 0 := by
    intro hzero
    have h := (LinearIndependent.pair_iff (R := F) (x := (1 : K)) (y := θ ^ e)).mp
      (independent_of_notMem he) r t
      (by simpa only [Algebra.smul_def, mul_one] using hzero)
    exact hrt.elim (fun hr => hr h.1) (fun ht => ht h.2)
  obtain ⟨k, hk⟩ := exists_pow_of_order hc hθ₀ hθ
  apply affine_of_shift hK hθ₀ hb he (k := k) <;> rw [hk, mem_plane]
  · exact ⟨t, r, add_comm ..⟩
  · refine ⟨-w, s, ?_⟩
    rw [map_neg, hs, pow_add]
    dsimp [c]
    ring

end zModAffinelyEquivalent_singerSet

open zModAffinelyEquivalent_singerSet in
/-- **Affine equivalences between Singer sets.** Let $F$ be a finite field with $q$ elements and
characteristic $p$, let $h \ge 2$, let $K$ be a field extension of $F$ of degree $h + 1$, and
let $\theta \in K$ have order $|K| - 1$, that is, generate $K^\times$. Put
$M = (q^{h+1} - 1)/(q - 1)$. Let $b$ and $e$ be natural numbers such that the minimal
polynomials of $\theta^b$ and $\theta^e$ over $F$ both have degree $h + 1$. Suppose that
(iv) $b \equiv e \pmod{M}$, or (v) $b \equiv p^i e \pmod{q^{h+1} - 1}$ for some natural number
$i$, or (vi) $\theta^b - \theta^e \in F$, or (vii) $r\theta^b + t\theta^{e+b} + w\theta^e \in F$
for some $r, t, w \in F$ with $r$ and $t$ not both $0$. Then the Singer sets
$\mathrm{Singer}_h(q, b)$ and $\mathrm{Singer}_h(q, e)$ built from $F$, $K$ and $\theta$ are
affinely equivalent.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 4 (items (iv)–(vii)) (`jis-2024-24.1.2-thm-4`). -/
public theorem zModAffinelyEquivalent_singerSet {F K : Type*} [Field F] [Fintype F]
    [Field K] [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h)
    (hK : Module.finrank F K = h + 1) {θ : K} (hθ : orderOf θ = Fintype.card K - 1) {b e : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h + 1)
    (he : (minpoly F (θ ^ e)).natDegree = h + 1)
    (hbe : b ≡ e [MOD (Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1)] ∨
      (∃ i : ℕ, b ≡ ringChar F ^ i * e [MOD Fintype.card F ^ (h + 1) - 1]) ∨
      θ ^ b - θ ^ e ∈ Set.range (algebraMap F K) ∨
      ∃ r t w : F, (r ≠ 0 ∨ t ≠ 0) ∧
        algebraMap F K r * θ ^ b + algebraMap F K t * θ ^ (e + b) +
          algebraMap F K w * θ ^ e ∈ Set.range (algebraMap F K)) :
    ZModAffinelyEquivalent (singerSet F h θ b) (singerSet F h θ e) := by
  let q := Fintype.card F
  have hq : 1 < q := Fintype.one_lt_card
  have hcard : Fintype.card K = q ^ (h + 1) := by
    rw [Module.card_eq_pow_finrank (K := F), hK]
  have : NeZero ((q ^ (h + 1) - 1) / (q - 1)) :=
    ⟨(Nat.div_pos (Nat.sub_le_sub_right (Nat.le_pow (by omega)) 1) (by omega)).ne'⟩
  have hord : 0 < orderOf θ := by
    rw [hθ]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have hθ₀ : θ ≠ 0 := by
    rintro rfl
    simp at hord
  have hb' : θ ^ b ∉ (algebraMap F K).range := fun hx => by
    have := minpoly.natDegree_eq_one_iff.mpr hx
    omega
  have he' : θ ^ e ∉ (algebraMap F K).range := fun hx => by
    have := minpoly.natDegree_eq_one_iff.mpr hx
    omega
  have hone : (1 : K) ∈ plane F (θ ^ e) := Submodule.subset_span (by simp)
  have hy : θ ^ e ∈ plane F (θ ^ e) := Submodule.subset_span (by simp)
  rcases hbe with hmod | ⟨i, hi⟩ | ⟨v, hv⟩ | ⟨r, t, w, hrt, s, hs⟩
  · apply affine_of_shift hK hθ₀ hb' he' (k := 0) (by simpa)
    simp only [pow_zero, one_mul]
    apply (pow_mem_mod_iff hK hθ₀ _ b).mp
    rw [hmod]
    exact (pow_mem_mod_iff hK hθ₀ _ e).mpr hy
  · apply affine_of_frobenius hK hθ₀ (i := i)
    rw [← pow_mul, mul_comm, (orderOf_pos_iff.mp hord).pow_eq_pow_iff_modEq, hθ, hcard]
    exact hi
  · apply affine_of_shift hK hθ₀ hb' he' (k := 0) (by simpa)
    simp only [pow_zero, one_mul]
    exact mem_plane.mpr ⟨1, v, by rw [map_one, one_mul, hv]; ring⟩
  · exact affine_of_relation hK hθ₀ hθ hb' he' hrt hs

end

end MetaMathlibExt
