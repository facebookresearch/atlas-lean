/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.TensorNormalization
public import Mathlib.RingTheory.Congruence.Hom

/-!
# Ordered-word PBW for the native universal enveloping algebra

The computed tensor normalizer defines a contextual ring congruence. Its
quotient receives the original Lie algebra because the actual relation
errors vanish. The native UEA universal property then gives coordinates on
the original UEA. These coordinates recover each ordered word, and the
already constructed spanning theorem gives an ordered-word basis.

No PBW, confluence, injectivity, or freeness conclusion is supplied as data.
The auxiliary quotient is used to construct coordinates; the resulting basis
and injectivity theorems concern the original native UEA.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

attribute [local implicit_reducible] RingCon.Quotient

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "T" => TensorAlgebra R L
local notation "U" => UniversalEnvelopingAlgebra R L
local notation "N" => (OrderedWord I →₀ R)
local notation "τ" => TensorAlgebra.ι R

attribute [local instance] LieRing.ofAssociativeRing

/-- The contextual congruence computed from the actual tensor normalizer. -/
@[implicit_reducible]
def normalizationRingCon (b : Module.Basis I R L) : RingCon T where
  r a c := ∀ p s : T, tensorNormalizer b (p * a * s) = tensorNormalizer b (p * c * s)
  iseqv :=
    { refl := by intro a p s; rfl
      symm := by intro a c h p s; exact (h p s).symm
      trans := by intro a c d h k p s; exact (h p s).trans (k p s) }
  add' := by
    intro a c d e hac hde p s
    simp only [mul_add, add_mul, map_add]
    rw [hac p s, hde p s]
  mul' := by
    intro a c d e hac hde p s
    calc
      tensorNormalizer b (p * (a * d) * s) =
          tensorNormalizer b (p * a * (d * s)) := by simp only [mul_assoc]
      _ = tensorNormalizer b (p * c * (d * s)) := hac p (d * s)
      _ = tensorNormalizer b ((p * c) * d * s) := by simp only [mul_assoc]
      _ = tensorNormalizer b ((p * c) * e * s) := hde (p * c) s
      _ = tensorNormalizer b (p * (c * e) * s) := by simp only [mul_assoc]

/-- The native defining Lie relation belongs to the constructed contextual
congruence, by the actual normalizer's annihilation theorem. -/
theorem normalizationRingCon_lie_compat (b : Module.Basis I R L) (x y : L) :
    normalizationRingCon b (τ ⁅x, y⁆ + τ y * τ x) (τ x * τ y) := by
  intro p s
  have hzero := tensorNormalizer_relationError b p s x y
  simp only [relationError, mul_sub, sub_mul, map_sub] at hzero
  simp only [mul_add, add_mul, map_add]
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hzero)).symm

/-- An auxiliary ring quotient constructed from actual normalization. -/
abbrev NormalizationQuotient (b : Module.Basis I R L) :=
  (normalizationRingCon b).Quotient

/-- The original tensor algebra maps to the auxiliary quotient. -/
@[implicit_reducible]
def normalizationQuotientMap (b : Module.Basis I R L) : T →ₐ[R] NormalizationQuotient b :=
  RingCon.mkₐ R (normalizationRingCon b)

theorem normalizationQuotientMap_surjective (b : Module.Basis I R L) :
    Function.Surjective (normalizationQuotientMap b) :=
  RingCon.mkₐ_surjective (normalizationRingCon b)

/-- The computed normal form is well-defined and linear on the auxiliary
quotient, since its contextual congruence includes the empty context. -/
def normalizationQuotientCoordinates (b : Module.Basis I R L) :
    NormalizationQuotient b →ₗ[R] N where
  toFun := Quotient.lift (tensorNormalizer b) (by
    intro a c h
    simpa only [one_mul, mul_one] using h (1 : T) (1 : T))
  map_add' x y := by
    obtain ⟨a, rfl⟩ := normalizationQuotientMap_surjective b x
    obtain ⟨c, rfl⟩ := normalizationQuotientMap_surjective b y
    have hadd : normalizationQuotientMap b (a + c) =
        normalizationQuotientMap b a + normalizationQuotientMap b c :=
      (normalizationQuotientMap b).toLinearMap.map_add a c
    rw [← hadd]
    change tensorNormalizer b (a + c) = tensorNormalizer b a + tensorNormalizer b c
    exact (tensorNormalizer b).map_add a c
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := normalizationQuotientMap_surjective b x
    have hsmul : normalizationQuotientMap b (r • a) = r • normalizationQuotientMap b a :=
      (normalizationQuotientMap b).toLinearMap.map_smul r a
    rw [← hsmul]
    change tensorNormalizer b (r • a) = (RingHom.id R) r • tensorNormalizer b a
    simpa only [RingHom.id_apply] using (tensorNormalizer b).map_smul r a

@[simp]
theorem normalizationQuotientCoordinates_mk (b : Module.Basis I R L) (a : T) :
    normalizationQuotientCoordinates b (normalizationQuotientMap b a) =
      tensorNormalizer b a := rfl

/-- The original Lie generators map to the auxiliary quotient with their
actual bracket relation, proved from normalization. -/
def normalizationQuotientι (b : Module.Basis I R L) : L →ₗ⁅R⁆ NormalizationQuotient b where
  toLinearMap := (normalizationQuotientMap b).toLinearMap.comp τ
  map_lie' := by
    intro x y
    change normalizationQuotientMap b (τ ⁅x, y⁆) =
      normalizationQuotientMap b (τ x) * normalizationQuotientMap b (τ y) -
        normalizationQuotientMap b (τ y) * normalizationQuotientMap b (τ x)
    have h : normalizationQuotientMap b (τ ⁅x, y⁆ + τ y * τ x) =
        normalizationQuotientMap b (τ x * τ y) :=
      Quotient.sound (normalizationRingCon_lie_compat b x y)
    simp only [map_add, map_mul] at h
    exact eq_sub_iff_add_eq.mpr h

@[simp]
theorem normalizationQuotientι_apply (b : Module.Basis I R L) (x : L) :
    normalizationQuotientι b x = normalizationQuotientMap b (τ x) := rfl

/-- Coordinates on the original native UEA, obtained by its native universal
property from the actually constructed Lie map and normalizer quotient. -/
def pbwCoordinates (b : Module.Basis I R L) : U →ₗ[R] N :=
  (normalizationQuotientCoordinates b).comp
    (UniversalEnvelopingAlgebra.lift R (normalizationQuotientι b)).toLinearMap

theorem lift_normalizationQuotientι_basisWord (b : Module.Basis I R L) (xs : List I) :
    UniversalEnvelopingAlgebra.lift R (normalizationQuotientι b) (basisWord b xs) =
      normalizationQuotientMap b (tensorWord b xs) := by
  induction xs with
  | nil => simp only [basisWord_nil, tensorWord_nil, map_one]
  | cons i xs ih =>
      simp only [basisWord_cons, tensorWord_cons, map_mul,
        UniversalEnvelopingAlgebra.lift_ι_apply, normalizationQuotientι_apply, ih]

/-- The native UEA coordinates compute the actual word normalizer. -/
@[simp]
theorem pbwCoordinates_basisWord (b : Module.Basis I R L) (xs : List I) :
    pbwCoordinates b (basisWord b xs) = normalize b xs := by
  change normalizationQuotientCoordinates b
    (UniversalEnvelopingAlgebra.lift R (normalizationQuotientι b) (basisWord b xs)) = _
  rw [lift_normalizationQuotientι_basisWord, normalizationQuotientCoordinates_mk,
    tensorNormalizer_tensorWord]

/-- The original ordered-word evaluation has the constructed PBW coordinates
as a left inverse. -/
theorem pbwCoordinates_comp_orderedWordLinear (b : Module.Basis I R L) :
    (pbwCoordinates b).comp (orderedWordLinear b) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro xs r
  rw [LinearMap.comp_apply, orderedWordLinear_single, map_smul,
    orderedWordValue, pbwCoordinates_basisWord, normalize_ordered]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

/-- Actual ordered words are linearly independent and spanning in the original
native UEA, giving its explicit coefficient equivalence. -/
def orderedWordEquiv (b : Module.Basis I R L) : N ≃ₗ[R] U :=
  LinearEquiv.ofBijective (orderedWordLinear b) ⟨
    (show Function.LeftInverse (pbwCoordinates b) (orderedWordLinear b) from
      fun x => LinearMap.congr_fun (pbwCoordinates_comp_orderedWordLinear b) x).injective,
    (LinearMap.range_eq_top.mp (by
      rw [orderedWordLinear, Finsupp.range_linearCombination, orderedWord_spanning]))⟩

/-- The actual ordered-word PBW basis of the original native UEA. -/
def orderedBasis (b : Module.Basis I R L) : Module.Basis (OrderedWord I) R U :=
  (Finsupp.basisSingleOne (R := R)).map (orderedWordEquiv b)

@[simp]
theorem orderedBasis_apply (b : Module.Basis I R L) (xs : OrderedWord I) :
    orderedBasis b xs = orderedWordValue b xs := by
  change orderedWordLinear b (Finsupp.single xs 1) = orderedWordValue b xs
  rw [orderedWordLinear_single, one_smul]

theorem orderedWord_linearIndependent (b : Module.Basis I R L) :
    LinearIndependent R (orderedWordValue b) := by
  have h : (orderedBasis b : OrderedWord I → U) = orderedWordValue b :=
    funext (orderedBasis_apply b)
  rw [← h]
  exact (orderedBasis b).linearIndependent

/-- PBW freeness for the actual native UEA over an arbitrary free-basis ground module. -/
theorem free_of_basis (b : Module.Basis I R L) : Module.Free R U :=
  Module.Free.of_basis (orderedBasis b)

/-- PBW freeness requires only freeness of the underlying Lie module. -/
theorem free_of_free [Module.Free R L] : Module.Free R U := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  exact free_of_basis (Module.Free.chooseBasis R L)

/-- The degree-one coefficient extractor obtained from the actual PBW coordinates. -/
def degreeOneProjection (b : Module.Basis I R L) : U →ₗ[R] L :=
  (Finsupp.linearCombination R (fun xs : OrderedWord I =>
    match xs.val with
    | [i] => b i
    | _ => 0)).comp (pbwCoordinates b)

theorem degreeOneProjection_comp_ι (b : Module.Basis I R L) :
    (degreeOneProjection b).comp (UniversalEnvelopingAlgebra.ι R).toLinearMap =
      LinearMap.id := by
  apply b.ext
  intro i
  have hword : UniversalEnvelopingAlgebra.ι R (b i) = basisWord b [i] := by
    simp only [basisWord_cons, basisWord_nil, mul_one]
  let xs : OrderedWord I := ⟨[i], by simp⟩
  change Finsupp.linearCombination R (fun ys : OrderedWord I =>
      match ys.val with
      | [j] => b j
      | _ => 0) (pbwCoordinates b (UniversalEnvelopingAlgebra.ι R (b i))) = b i
  rw [hword, pbwCoordinates_basisWord]
  change Finsupp.linearCombination R _ (normalize b xs.val) = b i
  rw [normalize_ordered b xs, Finsupp.linearCombination_single, one_smul]

/-- The original Lie map into its native UEA is injective when an actual
ground-module basis is given. -/
theorem ι_injective_of_basis (b : Module.Basis I R L) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R (L := L)) := by
  intro x y hxy
  have hx := LinearMap.congr_fun (degreeOneProjection_comp_ι b) x
  have hy := LinearMap.congr_fun (degreeOneProjection_comp_ι b) y
  have h := congrArg (degreeOneProjection b) hxy
  exact hx.symm.trans (h.trans hy)

theorem ι_injective_of_free [Module.Free R L] :
    Function.Injective (UniversalEnvelopingAlgebra.ι R (L := L)) := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  exact ι_injective_of_basis (Module.Free.chooseBasis R L)

end UniversalEnvelopingAlgebra.PBW
