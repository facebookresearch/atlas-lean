/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.LinearAlgebra.Pi

/-!
# Regular orbits from `p`-regular orbits

Zenkov's counterexample to Kourovka Notebook Problem 12.25 has a `p`-regular orbit
for every prime and no regular orbit. We realize the action on five copies of the
four-element field over the two-element field. The units act by independent coordinate
multiplications, and a cyclic group of order five rotates the coordinates.
-/

noncomputable section

namespace MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25Wanted

/-- **Zhang's question on regular orbits from $p$-regular orbits.** The statement that for every
finite field $F$, every nonzero finite-dimensional vector space $V$ over $F$ and every finite group
$G$ acting faithfully on $V$ by $F$-linear maps, if the only $G$-invariant subspaces of $V$ are $0$
and $V$, and for every prime $p$ some vector of $V$ has a stabilizer in $G$ of order prime to $p$
(a $p$-regular orbit), then some vector of $V$ has trivial stabilizer in $G$ (a regular orbit).

This is Kourovka Notebook Problem 12.25 (Jiping Zhang). -/
@[expose] public def pRegularOrbitsImplyRegularOrbit : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] (G : Type) [Group G] [Finite G]
    [DistribMulAction G V] [SMulCommClass G F V], FaithfulSMul G V →
    (∀ W : Submodule F V, (∀ g : G, ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ p : ℕ, p.Prime → ∃ v : V, (Nat.card (MulAction.stabilizer G v)).Coprime p) →
    ∃ v : V, MulAction.stabilizer G v = ⊥

private abbrev K := GaloisField 2 2
private abbrev Q := Multiplicative (ZMod 5)
private abbrev V := Q → K
private abbrev G := Kˣ ≀ᵣ Q

private theorem card_field : Nat.card K = 4 := GaloisField.card 2 2 (by decide)

private theorem card_units : Nat.card Kˣ = 3 := by rw [Nat.card_units, card_field]

private theorem card_rotations : Nat.card Q = 5 := Nat.card_zmod 5

local instance monomialSMul : SMul G V where
  smul g v i := (g.left i : K) * v (g.right⁻¹ * i)

private theorem smul_apply (g : G) (v : V) (i : Q) :
    (g • v) i = (g.left i : K) * v (g.right⁻¹ * i) := rfl

local instance monomialAction : DistribMulAction G V where
  one_smul v := by ext; simp [smul_apply]
  mul_smul g h v := by ext; simp [smul_apply, mul_assoc]
  smul_zero g := by ext; simp [smul_apply]
  smul_add g v w := by ext; simp [smul_apply, mul_add]

local instance commuteScalars : SMulCommClass G (ZMod 2) V where
  smul_comm g c v := by ext; simp [smul_apply]

-- The positions with value zero rotate according to the right component.
private def oneZero : V := fun i ↦ if i = 1 then 0 else 1

private theorem smul_oneZero_eq_zero_iff (g : G) (i : Q) :
    (g • oneZero) i = 0 ↔ g.right = i := by
  simp [smul_apply, oneZero, inv_mul_eq_one]

private theorem faithful : FaithfulSMul G V where
  eq_of_smul_eq_smul {g h} heq := by
    apply RegularWreathProduct.ext
    · funext i
      apply Units.ext
      simpa [smul_apply] using congrFun (heq (fun _ ↦ 1)) i
    · apply (smul_oneZero_eq_zero_iff g h.right).mp
      rw [heq oneZero]
      exact (smul_oneZero_eq_zero_iff h h.right).mpr rfl

private theorem smul_single (g : G) (i : Q) (a : K) :
    g • (Pi.single i a : V) = Pi.single (g.right * i) ((g.left (g.right * i) : K) * a) := by
  ext j
  by_cases h : j = g.right * i
  · subst j
    simp [smul_apply]
  · have h' : g.right⁻¹ * j ≠ i := fun e ↦ h (inv_mul_eq_iff_eq_mul.mp e)
    simp [smul_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

private theorem irreducible (W : Submodule (ZMod 2) V)
    (hW : ∀ g : G, ∀ v ∈ W, g • v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  apply or_iff_not_imp_left.mpr
  intro h
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv0
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_units]; decide)
  obtain ⟨u, hu⟩ := exists_ne (1 : Kˣ)
  -- Subtracting a diagonal translate isolates a nonzero entry on the i-th axis.
  let a := (u : K) * v i - v i
  have ha : a ≠ 0 := by
    apply sub_ne_zero.mpr
    rw [ne_eq, mul_eq_right₀ hi]
    exact fun e ↦ hu (Units.ext e)
  let d : G := ⟨Pi.mulSingle i u, 1⟩
  have hd : d • v - v = Pi.single i a := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [d, smul_apply, a]
    · simp [d, smul_apply, Pi.mulSingle_eq_of_ne hj, Pi.single_eq_of_ne hj]
  have haxis : Pi.single i a ∈ W := hd ▸ W.sub_mem (hW d v hv) hv
  -- Rotations and unit multipliers now give every entry on every axis.
  have hall (j : Q) (b : K) : Pi.single j b ∈ W := by
    by_cases hb : b = 0
    · simp [hb]
    let g : G := ⟨fun _ ↦ Units.mk0 (b / a) (div_ne_zero hb ha), j * i⁻¹⟩
    simpa [smul_single, g, ha] using hW g _ haxis
  apply top_unique
  intro w _
  rw [← Finset.univ_sum_single w]
  exact W.sum_mem fun j _ ↦ hall j (w j)

-- The constant vector one is fixed precisely by the pure rotations.
private theorem card_stabilizer_one : Nat.card (MulAction.stabilizer G (1 : V)) = 5 := by
  let e : MulAction.stabilizer G (1 : V) ≃ Q :=
    { toFun := fun g ↦ g.val.right
      invFun := fun q ↦ ⟨⟨1, q⟩, by
        apply MulAction.mem_stabilizer_iff.mpr
        ext i
        simp [smul_apply]⟩
      left_inv := by
        intro g
        apply Subtype.ext
        refine RegularWreathProduct.ext ?_ rfl
        funext i
        apply Units.ext
        simpa [smul_apply] using (congrFun (MulAction.mem_stabilizer_iff.mp g.property) i).symm
      right_inv := fun _ ↦ rfl }
  exact (Nat.card_congr e).trans card_rotations

-- The unique zero rules out every nonidentity rotation. Only its multiplier is free.
private theorem card_stabilizer_oneZero : Nat.card (MulAction.stabilizer G oneZero) = 3 := by
  let e : MulAction.stabilizer G oneZero ≃ Kˣ :=
    { toFun := fun g ↦ g.val.left 1
      invFun := fun u ↦ ⟨⟨Pi.mulSingle 1 u, 1⟩, by
        apply MulAction.mem_stabilizer_iff.mpr
        ext i
        by_cases hi : i = 1 <;> simp [smul_apply, oneZero, hi]⟩
      left_inv := by
        intro g
        have hfix := MulAction.mem_stabilizer_iff.mp g.property
        have hrot : g.val.right = 1 := (smul_oneZero_eq_zero_iff _ _).mp (by
          rw [hfix]
          simp [oneZero])
        apply Subtype.ext
        refine RegularWreathProduct.ext ?_ hrot.symm
        funext i
        by_cases hi : i = 1
        · simp [hi]
        · apply Units.ext
          simpa [smul_apply, oneZero, hi, hrot, Pi.mulSingle_eq_of_ne hi] using
            (congrFun hfix i).symm
      right_inv := fun u ↦ Pi.mulSingle_eq_same (M := fun _ : Q ↦ Kˣ) 1 u }
  exact (Nat.card_congr e).trans card_units

private theorem prime_regular (p : ℕ) (hp : p.Prime) :
    ∃ v : V, (Nat.card (MulAction.stabilizer G v)).Coprime p := by
  by_cases h : p = 5
  · subst p
    exact ⟨oneZero, by rw [card_stabilizer_oneZero]; decide⟩
  · refine ⟨1, ?_⟩
    rw [card_stabilizer_one]
    exact (Nat.coprime_primes (by decide) hp).mpr (Ne.symm h)

private theorem no_regular_orbit (v : V) : MulAction.stabilizer G v ≠ ⊥ := by
  intro h
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G v)
  rw [Nat.card_prod, h, Subgroup.card_bot, mul_one, RegularWreathProduct.card,
    card_units, card_rotations] at hc
  have hle := Nat.card_le_card_of_injective (Subtype.val : MulAction.orbit G v → V)
    Subtype.val_injective
  rw [hc, Nat.card_fun, card_field, card_rotations] at hle
  exact (by decide : ¬ 3 ^ 5 * 5 ≤ 4 ^ 5) hle

/--
**$p$-regular orbits for every prime do not force a regular orbit.** There exist a finite field $F$,
a nonzero finite-dimensional vector space $V$ over $F$ and a finite group $G$ acting faithfully on
$V$ by $F$-linear maps such that the only $G$-invariant subspaces of $V$ are $0$ and $V$ and, for
every prime $p$, some vector of $V$ has a stabilizer in $G$ of order prime to $p$, but no vector of
$V$ has trivial stabilizer in $G$.

Resolved false: the Kourovka Archive answers 12.25 "No, not always" (V. I. Zenkov). Write
$\mathbb{Z}_n$ for the cyclic group of order $n$, $A_4$ for the alternating group of degree $4$ and
$\mathbb{F}_2$ for the field with two elements. Let $H = A_4 \wr \mathbb{Z}_5$ be the wreath
product, let $V = O_2(H)$ be the largest normal $2$-subgroup of $H$, so $V \cong \mathbb{F}_2^{10}$,
and let $G \cong \mathbb{Z}_3 \wr \mathbb{Z}_5$ be a complement to $V$ in $H$. The faithful
irreducible action of $G$ on $V$ by conjugation has orbits with stabilizers of order $5$ and of
order $3$, hence $p$-regular orbits for every prime $p$, but no regular orbit, since
$|G| = 1215 > 1024 = |V|$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.25 (Jiping
Zhang); resolution: V. I. Zenkov, letter of 11 February 1994, as recorded in the Kourovka Archive,
Problem 12.25, Archive answer: No, not always; H = A_4 ≀ Z_5, V = O_2(H), G a complement to V acting
by conjugation, https://arxiv.org/abs/1401.0300v49.
-/
public theorem pRegularOrbitsImplyRegularOrbit_refuted : ¬ pRegularOrbitsImplyRegularOrbit := by
  intro claim
  obtain ⟨v, hv⟩ := claim (ZMod 2) V G faithful irreducible prime_regular
  exact no_regular_orbit v hv

end MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25Wanted
