/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.FiniteField.SmallBias
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Tests for finite-field parity counts

The concrete clients use the fields with `2 ^ 4` and `2 ^ 5` elements.  A
finite basis supplies the required binary coordinate equivalence.  The
singleton exponent sets give exactly 128 and 496 odd pairs, respectively;
the two-exponent set `{0, 1}` also gives 496 pairs and exercises its unique
polynomial root.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace FiniteField

noncomputable local instance galoisFintype (n : ℕ) :
    Fintype (GaloisField 2 n) :=
  Fintype.ofFinite _

/-- Binary coordinates on the field with `2 ^ n` elements. -/
private noncomputable def galoisBits (n : ℕ) (hn : n ≠ 0) :
    GaloisField 2 n ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 n)
    (GaloisField.finrank 2 hn)).equivFun

/-- The source's private `ip` is exactly Mathlib's `dotProduct`. -/
private def sourceIP {s : ℕ} (x y : Fin s → ZMod 2) : ZMod 2 :=
  ∑ i, x i * y i

private theorem sourceIP_eq_dotProduct {s : ℕ}
    (x y : Fin s → ZMod 2) :
    sourceIP x y = dotProduct x y :=
  rfl

/-- The source's odd-cardinality bridge, retained privately as a compatibility
check for the original count schema. -/
private theorem source_odd_card_iff_sum_eq_one {I : Type*}
    (T : Finset I) (f : I → ZMod 2) :
    Odd #{i ∈ T | f i = 1} ↔ ∑ i ∈ T, f i = 1 := by
  have h : ∀ c : ZMod 2, c = if c = 1 then 1 else 0 := by decide
  rw [← ZMod.natCast_eq_one_iff_odd, natCast_card_filter]
  rw [sum_congr rfl fun i _ ↦ h (f i)]

/-- The exact binary dot-product count over the 32-element field. -/
private theorem galois32_dotProduct_count :
    #{p : GaloisField 2 5 × GaloisField 2 5 |
      dotProduct (galoisBits 5 (by decide) p.1)
        (galoisBits 5 (by decide) p.2) = 1} = 496 := by
  classical
  let bits := galoisBits 5 (by decide)
  have hcount :
      #{p : GaloisField 2 5 × GaloisField 2 5 |
        dotProduct (bits p.1) (bits p.2) = 1} =
          #{p : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) |
            dotProduct p.1 p.2 = 1} := by
    exact Finset.card_equiv (bits.toEquiv.prodCongr bits.toEquiv) (by simp)
  have hbinary :
      #{p : (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2) |
        dotProduct p.1 p.2 = 1} = 496 := by
    set_option maxRecDepth 100000 in
      decide
  simpa [bits] using hcount.trans hbinary

/-- The dot product distinguishes the two coordinate directions. -/
example :
    dotProduct (![1, 0] : Fin 2 → ZMod 2) ![0, 1] = 0 ∧
      dotProduct (![1, 0] : Fin 2 → ZMod 2) ![1, 0] = 1 := by
  decide

/-- The zero vector has no partner with binary dot product one. -/
example : #{y : Fin 2 → ZMod 2 | dotProduct 0 y = 1} = 0 := by
  simp [dotProduct]

/-- With no exponents, the odd-parity pair count is zero. -/
example :
    #{_p : (ZMod 2) × (ZMod 2) |
      Odd #{_E ∈ (∅ : Finset (Fin 0)) | True}} = 0 := by
  decide

/-- The source-faithful count theorem needs only field, finiteness, binary
coordinates, and a nonempty exponent set. -/
example {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (V : Finset (Fin m)) (hV : V.Nonempty) :
    Fintype.card F ^ 2 ≤
      2 * #{p : F × F |
        Odd #{E ∈ V |
          dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}} +
        (m - 1) * Fintype.card F := by
  exact odd_dotProduct_power_count bits V hV

/-- The first public theorem is compatible with the source's exact private
inner-product schema. -/
example {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (V : Finset (Fin m)) (hV : V.Nonempty) :
    Fintype.card F ^ 2 ≤
      2 * #{p : F × F |
        Odd #{E ∈ V |
          sourceIP (bits (p.1 ^ E.val)) (bits p.2) = 1}} +
        (m - 1) * Fintype.card F := by
  change Fintype.card F ^ 2 ≤
    2 * #{p : F × F |
      Odd #{E ∈ V |
        dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}} +
      (m - 1) * Fintype.card F
  exact odd_dotProduct_power_count bits V hV

/-- The `15 / 32` public theorem has the exact source count schema. -/
example {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (h16 : 16 * m ≤ 2 ^ s) (V : Finset (Fin m)) (hV : V.Nonempty) :
    15 * Fintype.card F ^ 2 ≤
      32 * #{p : F × F |
        Odd #{E ∈ V |
          sourceIP (bits (p.1 ^ E.val)) (bits p.2) = 1}} := by
  change 15 * Fintype.card F ^ 2 ≤
    32 * #{p : F × F |
      Odd #{E ∈ V |
        dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}}
  exact odd_dotProduct_power_count_of_sixteen_mul_le bits h16 V hV

/-- The one-exponent public theorem has the exact source count schema. -/
example {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (E : Fin m) :
    2 * #{p : F × F |
      sourceIP (bits (p.1 ^ E.val)) (bits p.2) = 1} ≤
        Fintype.card F ^ 2 := by
  change 2 * #{p : F × F |
    dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1} ≤
      Fintype.card F ^ 2
  exact dotProduct_power_count_le_half bits E

/-- In `GaloisField 2 4`, exponent zero gives 128 odd pairs out of 256. -/
example :
    #{p : GaloisField 2 4 × GaloisField 2 4 |
      Odd #{E ∈ ({0} : Finset (Fin 1)) |
        dotProduct (galoisBits 4 (by decide) (p.1 ^ E.val))
          (galoisBits 4 (by decide) p.2) = 1}} = 128 := by
  classical
  have hlo := odd_dotProduct_power_count (galoisBits 4 (by decide))
    ({0} : Finset (Fin 1)) (by simp)
  have hhi := dotProduct_power_count_le_half
    (galoisBits 4 (by decide)) (0 : Fin 1)
  have hparity :
      #{p : GaloisField 2 4 × GaloisField 2 4 |
        Odd #{E ∈ ({0} : Finset (Fin 1)) |
          dotProduct (galoisBits 4 (by decide) (p.1 ^ E.val))
            (galoisBits 4 (by decide) p.2) = 1}} =
        #{p : GaloisField 2 4 × GaloisField 2 4 |
          dotProduct (galoisBits 4 (by decide) 1)
            (galoisBits 4 (by decide) p.2) = 1} := by
    exact Finset.card_equiv (Equiv.refl _) (by
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.refl_apply]
      by_cases hp : dotProduct (galoisBits 4 (by decide) 1)
          (galoisBits 4 (by decide) p.2) = 1
      · rw [show #{E ∈ ({0} : Finset (Fin 1)) |
            dotProduct (galoisBits 4 (by decide) (p.1 ^ E.val))
              (galoisBits 4 (by decide) p.2) = 1} = 1 by simp [hp]]
        exact iff_of_true odd_one hp
      · rw [show #{E ∈ ({0} : Finset (Fin 1)) |
            dotProduct (galoisBits 4 (by decide) (p.1 ^ E.val))
              (galoisBits 4 (by decide) p.2) = 1} = 0 by simp [hp]]
        exact iff_of_false Nat.not_odd_zero hp)
  have hcard : Fintype.card (GaloisField 2 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 4 (by decide)]
    decide
  rw [hparity] at hlo ⊢
  simp [hcard] at hlo hhi ⊢
  omega

/-- The `16 * m ≤ 2 ^ s` boundary is attained for the 16-element field and
the singleton exponent set. -/
example :
    15 * Fintype.card (GaloisField 2 4) ^ 2 ≤
      32 * #{p : GaloisField 2 4 × GaloisField 2 4 |
        Odd #{E ∈ ({0} : Finset (Fin 1)) |
          dotProduct (galoisBits 4 (by decide) (p.1 ^ E.val))
            (galoisBits 4 (by decide) p.2) = 1}} := by
  classical
  exact odd_dotProduct_power_count_of_sixteen_mul_le
    (galoisBits 4 (by decide)) (by decide) ({0} : Finset (Fin 1)) (by simp)

/-- In `GaloisField 2 5`, exponent one gives 496 odd pairs out of 1024. -/
example :
    #{p : GaloisField 2 5 × GaloisField 2 5 |
      Odd #{E ∈ ({1} : Finset (Fin 2)) |
        dotProduct (galoisBits 5 (by decide) (p.1 ^ E.val))
          (galoisBits 5 (by decide) p.2) = 1}} = 496 := by
  classical
  let bits := galoisBits 5 (by decide)
  have hparity :
      #{p : GaloisField 2 5 × GaloisField 2 5 |
        Odd #{E ∈ ({1} : Finset (Fin 2)) |
          dotProduct (galoisBits 5 (by decide) (p.1 ^ E.val))
            (galoisBits 5 (by decide) p.2) = 1}} =
        #{p : GaloisField 2 5 × GaloisField 2 5 |
          dotProduct (galoisBits 5 (by decide) p.1)
            (galoisBits 5 (by decide) p.2) = 1} := by
    change
      #{p : GaloisField 2 5 × GaloisField 2 5 |
        Odd #{E ∈ ({1} : Finset (Fin 2)) |
          dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}} =
        #{p : GaloisField 2 5 × GaloisField 2 5 |
          dotProduct (bits p.1) (bits p.2) = 1}
    exact Finset.card_equiv (Equiv.refl _) (by
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hp : dotProduct (bits p.1) (bits p.2) = 1
      · rw [show {E ∈ ({1} : Finset (Fin 2)) |
            dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1} = {1} by
          ext E
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · exact fun h ↦ h.1
          · intro hE
            subst E
            exact ⟨rfl, by simpa using hp⟩]
        simp only [Finset.card_singleton]
        exact iff_of_true odd_one hp
      · rw [show {E ∈ ({1} : Finset (Fin 2)) |
            dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1} = ∅ by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro E h
          simp only [Finset.mem_filter, Finset.mem_singleton] at h
          apply hp
          obtain ⟨rfl, h⟩ := h
          simpa using h]
        simp only [Finset.card_empty]
        exact iff_of_false Nat.not_odd_zero hp)
  rw [hparity]
  exact galois32_dotProduct_count

/-- For `{0, 1}`, the exponent sum survives at zero because `0 ^ 0 = 1`
and cancels at one in characteristic two. -/
example :
    ((0 : GaloisField 2 5) ^ 0 + 0 ^ 1 = 1) ∧
      ((1 : GaloisField 2 5) ^ 0 + 1 ^ 1 = 0) := by
  constructor
  · simp
  · have htwo : (1 : GaloisField 2 5) + 1 = 0 := by
      have h := congrArg (algebraMap (ZMod 2) (GaloisField 2 5))
        (show (1 : ZMod 2) + 1 = 0 by decide)
      simpa using h
    simpa using htwo

/-- In `GaloisField 2 5`, the genuine two-exponent family `{0, 1}` has 496
odd pairs.  Translation by one sends its polynomial `1 + X` to the direct
binary linear-form count. -/
example :
    #{p : GaloisField 2 5 × GaloisField 2 5 |
      Odd #{E ∈ ({0, 1} : Finset (Fin 2)) |
        dotProduct (galoisBits 5 (by decide) (p.1 ^ E.val))
          (galoisBits 5 (by decide) p.2) = 1}} = 496 := by
  classical
  let bits := galoisBits 5 (by decide)
  have hparity :
      #{p : GaloisField 2 5 × GaloisField 2 5 |
        Odd #{E ∈ ({0, 1} : Finset (Fin 2)) |
          dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}} =
        #{p : GaloisField 2 5 × GaloisField 2 5 |
          dotProduct (bits (p.1 + 1)) (bits p.2) = 1} := by
    exact Finset.card_equiv (Equiv.refl _) (by
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [source_odd_card_iff_sum_eq_one]
      have hsum :
          ∑ E ∈ ({0, 1} : Finset (Fin 2)),
              dotProduct (bits (p.1 ^ E.val)) (bits p.2) =
            dotProduct (bits (p.1 + 1)) (bits p.2) := by
        rw [show ({0, 1} : Finset (Fin 2)) = Finset.univ by decide,
          Fin.sum_univ_two]
        change dotProduct (bits (p.1 ^ 0)) (bits p.2) +
          dotProduct (bits (p.1 ^ 1)) (bits p.2) =
            dotProduct (bits (p.1 + 1)) (bits p.2)
        rw [pow_zero, pow_one, ← add_dotProduct, ← bits.map_add,
          add_comm]
      rw [hsum]
      rfl)
  have htranslate :
      #{p : GaloisField 2 5 × GaloisField 2 5 |
        dotProduct (bits (p.1 + 1)) (bits p.2) = 1} =
        #{p : GaloisField 2 5 × GaloisField 2 5 |
          dotProduct (bits p.1) (bits p.2) = 1} := by
    exact Finset.card_equiv
      ((Equiv.addRight (1 : GaloisField 2 5)).prodCongr (Equiv.refl _)) (by simp)
  rw [hparity, htranslate]
  exact galois32_dotProduct_count

/-- The `16 * m ≤ 2 ^ s` boundary is also attained for two exponents over
the 32-element field. -/
example :
    15 * Fintype.card (GaloisField 2 5) ^ 2 ≤
      32 * #{p : GaloisField 2 5 × GaloisField 2 5 |
        Odd #{E ∈ ({1} : Finset (Fin 2)) |
          dotProduct (galoisBits 5 (by decide) (p.1 ^ E.val))
            (galoisBits 5 (by decide) p.2) = 1}} := by
  classical
  exact odd_dotProduct_power_count_of_sixteen_mul_le
    (galoisBits 5 (by decide)) (by decide) ({1} : Finset (Fin 2)) (by simp)

end FiniteField
