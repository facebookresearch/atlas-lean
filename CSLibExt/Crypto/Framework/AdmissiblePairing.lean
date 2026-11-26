/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.BilinearGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import MathlibExt.Computability.Complexity

/-!
# Admissible bilinear pairings

A pairing is a homomorphism in each variable. Admissibility asks for non-degeneracy in each
prime-order group and one polynomial-time evaluation algorithm on the given representations,
uniform in the public group parameters. The input representations are fixed before the evaluator
is chosen; neither a separate lookup table for each parameter nor an algorithm for computing
exponent coordinates is part of the definition.

Boneh and Franklin, *Identity-Based Encryption from the Weil Pairing*, §3 (before §3.1), use a
single source group written additively. Kate, Zaverucha and Goldberg, *Polynomial Commitments*,
Appendix A, allow two source groups and use multiplicative notation.
-/

@[expose] public section

open MetaMathlibExt MetaMathlibExt.BitstringEncoding

namespace Cslib.Complexity

/-- A family of binary functions is uniformly polynomial-time on given bitstring encodings if
one polynomial-time machine evaluates it at every parameter. It receives the encoded triple
(parameter, first argument, second argument) and returns the encoding of the value. Only its
answers on valid triples are prescribed. The time bound is polynomial in the encoded input
length; it does not vary with the parameter. -/
def UniformlyPolyTime₂ {ι : Type*} {X Y Z : ι → Type*} [BitstringEncoding ι]
    [∀ i, BitstringEncoding (X i)] [∀ i, BitstringEncoding (Y i)] [∀ i, BitstringEncoding (Z i)]
    (f : (i : ι) → X i → Y i → Z i) : Prop :=
  ∃ run : List Bool → List Bool, ComplexityTheory.IsPolyTime run ∧
    ∀ i x y, run (delimit (bitEncode i) ++ bitEncode (x, y)) = bitEncode (f i x y)

end Cslib.Complexity

namespace Cslib.Crypto.Framework

variable {ι : Type*} {G H T : ι → Type*}
  [∀ i, CommGroup (G i)] [∀ i, CommGroup (H i)] [∀ i, CommGroup (T i)]
  [BitstringEncoding ι] [∀ i, BitstringEncoding (G i)] [∀ i, BitstringEncoding (H i)]
  [∀ i, BitstringEncoding (T i)]

/-- A family of bilinear pairings between groups of common prime order is admissible when
no pairing is identically one and one polynomial-time algorithm computes the pairings on the
specified bitstring encodings. A curried group homomorphism expresses bilinearity. Taking both
source groups and their encodings to be the same gives the symmetric case. -/
structure IsAdmissiblePairing (p : ι → ℕ) (e : (i : ι) → G i →* H i →* T i) : Prop where
  prime : ∀ i, (p i).Prime
  card_left : ∀ i, Nat.card (G i) = p i
  card_right : ∀ i, Nat.card (H i) = p i
  card_target : ∀ i, Nat.card (T i) = p i
  nondegenerate : ∀ i, ∃ x y, e i x y ≠ 1
  efficient : Cslib.Complexity.UniformlyPolyTime₂ (fun i x y ↦ e i x y)

/-- Raising the arguments of an admissible pairing to powers $a$ and $b$ in the residue field
raises the pairing value to the product $ab$ in that field. Exponents are read via their
natural representatives. -/
theorem IsAdmissiblePairing.apply_pow_val {p : ι → ℕ} {e : (i : ι) → G i →* H i →* T i}
    (h : IsAdmissiblePairing p e) (i : ι) (x : G i) (y : H i) (a b : ZMod (p i)) :
    e i (x ^ a.val) (y ^ b.val) = (e i x y) ^ (a * b).val := by
  rw [map_pow, map_pow, MonoidHom.pow_apply, ← pow_mul, ZMod.val_mul]
  simpa only [h.card_target i] using (pow_mod_natCard (e i x y) (a.val * b.val)).symm

/-- The pairing of any generators of the two source groups generates the target. In the
symmetric case this applies in particular to a generator paired with itself. -/
theorem IsAdmissiblePairing.zpowers_pairing_eq_top {p : ι → ℕ}
    {e : (i : ι) → G i →* H i →* T i} (h : IsAdmissiblePairing p e) (i : ι)
    {g : G i} {g' : H i} (hg : Subgroup.zpowers g = ⊤) (hg' : Subgroup.zpowers g' = ⊤) :
    Subgroup.zpowers (e i g g') = ⊤ := by
  have : Fact (p i).Prime := ⟨h.prime i⟩
  apply zpowers_eq_top_of_prime_card (h.card_target i)
  intro he
  obtain ⟨x, y, hxy⟩ := h.nondegenerate i
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg.ge (Subgroup.mem_top x))
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg'.ge (Subgroup.mem_top y))
  exact hxy (by simp [map_zpow, MonoidHom.zpow_apply, he])

/-- For equal source groups, swapping the arguments of an admissible pairing does not change
its value: write both arguments as powers of the same generator. -/
theorem IsAdmissiblePairing.apply_comm {p : ι → ℕ} {e : (i : ι) → G i →* G i →* T i}
    (h : IsAdmissiblePairing p e) (i : ι) (x y : G i) : e i x y = e i y x := by
  have : Fact (p i).Prime := ⟨h.prime i⟩
  have : IsCyclic (G i) := isCyclic_of_prime_card (h.card_left i)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G i)
  obtain ⟨a, rfl⟩ := hg x
  obtain ⟨b, rfl⟩ := hg y
  simp only [map_zpow, MonoidHom.zpow_apply, ← zpow_mul, mul_comm a b]

/-- The pairing of a bilinear group in exponent coordinates, bundled as a homomorphism in each
variable. This uses the two multiplication laws, not a choice of bitstring representation. -/
def BilinearGroupData.pairingHom (B : BilinearGroupData) : B.G1 →* B.G2 →* B.GT where
  toFun x := { toFun := B.e x, map_one' := B.e_one_right x, map_mul' := B.map_mul_right x }
  map_one' := MonoidHom.ext (fun y ↦ B.e_one_left y)
  map_mul' x x' := MonoidHom.ext (fun y ↦ B.map_mul_left x x' y)

/-- A family of bilinear groups in exponent coordinates gives admissible pairings if its orders
are prime and its pairing maps have a uniform polynomial-time evaluator on the supplied
encodings. No efficiency hypothesis on the exponent isomorphisms is needed. -/
theorem BilinearGroupData.isAdmissiblePairing (B : ι → BilinearGroupData)
    [∀ i, BitstringEncoding (B i).G1] [∀ i, BitstringEncoding (B i).G2]
    [∀ i, BitstringEncoding (B i).GT] (hp : ∀ i, (B i).q.Prime)
    (he : Cslib.Complexity.UniformlyPolyTime₂ (fun i ↦ (B i).e)) :
    IsAdmissiblePairing (fun i ↦ (B i).q) (fun i ↦ (B i).pairingHom) where
  prime := hp
  card_left i := by rw [← Nat.card_congr (B i).exp1.toEquiv]; exact Nat.card_zmod _
  card_right i := by rw [← Nat.card_congr (B i).exp2.toEquiv]; exact Nat.card_zmod _
  card_target i := by rw [← Nat.card_congr (B i).expT.toEquiv]; exact Nat.card_zmod _
  nondegenerate i := ⟨(B i).g1, (B i).g2, (B i).e_g1_g2_ne_one⟩
  efficient := he

end Cslib.Crypto.Framework
