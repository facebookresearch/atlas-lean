/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The strict-affinoid predicate and its surjective-image and quotient proofs
adapt TauCetiProject/TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/RingTheory/Affinoid/Basic.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: The Tau Ceti contributors.
Modifications: use Mathlib's Restricted wrapper; distinguish the algebraic
strict predicate from a Banach affinoid with a positive real polyradius and
its quotient topology. The bounded spectra and analytic interfaces are new.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Affinoid algebras and actual bounded multiplicative spectra

An affinoid algebra has an actual complete ultrametric normed ring, a finite
restricted-series presentation, and a norm equivalent to that presentation's
quotient Gauss norm. Positive real polyradii include non-strict affinoids.
Points are actual bounded multiplicative real seminorms extending the ground
field norm. The weak topology and all maps are fixed by evaluation.

The source already proves strict-affinoid algebra primitives. Its separate
global adic gluing theorems are also available; they are not requested here.
A comparison with the weak real-seminorm topology is additional typed data.

References: Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields*, §§1.2 and 2.1–2.2; Zomervrucht, *Berkovich
analytification*, the unnumbered affinoid formulas before Remark 1.1, p. 1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces

open CategoryTheory Opposite

variable (K : Type) [NormedField K] [hKUltra : IsUltrametricDist K]

/-- The already source-defined algebraic strict-affinoid criterion. -/
def IsStrictAffinoid (A : Type) [CommRing A] [Algebra K A] : Prop :=
  ∃ (n : ℕ) (π : MvPowerSeries.Restricted K (fun _ : Fin n ↦ 1) →ₐ[K] A),
    Function.Surjective π

namespace IsStrictAffinoid

variable {K} {A B : Type} [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- Surjective images retain their actual finite Tate presentation. -/
theorem of_surjective (hA : IsStrictAffinoid K A) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : IsStrictAffinoid K B := by
  obtain ⟨n, π, hπ⟩ := hA
  exact ⟨n, f.comp π, hf.comp hπ⟩

/-- The algebraic predicate retains nilpotents and the zero quotient. -/
theorem quotient (hA : IsStrictAffinoid K A) (I : Ideal A) :
    IsStrictAffinoid K (A ⧸ I) :=
  hA.of_surjective (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I)

end IsStrictAffinoid

/-- The quotient Gauss seminorm determined by the actual presentation. -/
def quotientGaussNorm {A : Type} [CommRing A] [Algebra K A]
    {n : ℕ} {r : Fin n → ℝ}
    (π : MvPowerSeries.Restricted K r →ₐ[K] A) (a : A) : ℝ :=
  sInf {v | ∃ f : MvPowerSeries.Restricted K r,
    π f = a ∧ v = MvPowerSeries.gaussNorm (fun c : K ↦ ‖c‖) r f.1}

/-- An admissible finite Banach presentation, with its quotient norm fixed. -/
structure AffinoidPresentation (A : Type) [NormedCommRing A] [Algebra K A] where
  variableCount : ℕ
  radius : Fin variableCount → ℝ
  radius_pos : ∀ i, 0 < radius i
  quotientMap : MvPowerSeries.Restricted K radius →ₐ[K] A
  surjective : Function.Surjective quotientMap
  norm_equivalent : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : A,
    c * quotientGaussNorm K quotientMap a ≤ ‖a‖ ∧
      ‖a‖ ≤ C * quotientGaussNorm K quotientMap a

/-- Actual Banach affinoid algebras, including arbitrary positive polyradii. -/
structure AffinoidAlgebra where
  carrier : Type
  [normedCommRing : NormedCommRing carrier]
  [ultrametric : IsUltrametricDist carrier]
  [complete : CompleteSpace carrier]
  [algebra : Algebra K carrier]
  [normedAlgebra : NormedAlgebra K carrier]
  presentation : AffinoidPresentation K carrier

attribute [instance] AffinoidAlgebra.normedCommRing
  AffinoidAlgebra.ultrametric AffinoidAlgebra.complete
  AffinoidAlgebra.algebra AffinoidAlgebra.normedAlgebra

instance : CoeSort (AffinoidAlgebra K) Type := ⟨AffinoidAlgebra.carrier⟩

namespace AffinoidAlgebra

variable {K} (A B C : AffinoidAlgebra K)

/-- Actual bounded homomorphisms of the specified Banach algebras. -/
structure Hom where
  hom : A →ₐ[K] B
  bound : ∃ C : ℝ, 0 < C ∧ ∀ a : A, ‖hom a‖ ≤ C * ‖a‖

include hKUltra in
@[ext]
theorem Hom.ext {f g : Hom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def Hom.id : Hom A A where
  hom := AlgHom.id K A
  bound := ⟨1, zero_lt_one, by simp⟩

def Hom.comp (f : Hom A B) (g : Hom B C) : Hom A C where
  hom := g.hom.comp f.hom
  bound := by
    obtain ⟨cf, hcf, hf⟩ := f.bound
    obtain ⟨cg, hcg, hg⟩ := g.bound
    refine ⟨cg * cf, mul_pos hcg hcf, fun a ↦ ?_⟩
    calc
      ‖g.hom (f.hom a)‖ ≤ cg * ‖f.hom a‖ := hg _
      _ ≤ cg * (cf * ‖a‖) := mul_le_mul_of_nonneg_left (hf a) hcg.le
      _ = (cg * cf) * ‖a‖ := (mul_assoc _ _ _).symm

instance : Category (AffinoidAlgebra K) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp _ _ _ f g
  id_comp f := Hom.ext _ _ (by ext a; rfl)
  comp_id f := Hom.ext _ _ (by ext a; rfl)
  assoc f g h := Hom.ext _ _ (by ext a; rfl)

end AffinoidAlgebra

variable {K} (A : AffinoidAlgebra K)

/-- An actual Berkovich point of a Banach algebra, with boundedness recorded. -/
structure BoundedPoint where
  seminorm : MulRingSeminorm A
  ultrametric : ∀ a b, seminorm (a + b) ≤ max (seminorm a) (seminorm b)
  extends_norm : ∀ a : K, seminorm (algebraMap K A a) = ‖a‖
  bounded : ∃ C : ℝ, 0 < C ∧ ∀ a : A, seminorm a ≤ C * ‖a‖

/-- The weak topology is precisely the topology of all real evaluations. -/
instance boundedPointTopology : TopologicalSpace (BoundedPoint A) :=
  TopologicalSpace.induced (fun p : BoundedPoint A ↦ fun a : A ↦ p.seminorm a)
    inferInstance

def spectrum : TopCat := TopCat.of (BoundedPoint A)

include hKUltra in
theorem continuous_evaluation (a : A) :
    Continuous (fun p : BoundedPoint A ↦ p.seminorm a) :=
  (continuous_apply a).comp continuous_induced_dom

variable {A} {B : AffinoidAlgebra K}

/-- Pull back the multiplicative seminorm along the actual algebra map. -/
def comapPoint (f : A ⟶ B) (p : BoundedPoint B) : BoundedPoint A where
  seminorm :=
    { toFun a := p.seminorm (f.hom a)
      map_zero' := by simp only [map_zero]
      neg' a := by simp only [map_neg, map_neg_eq_map]
      add_le' a b := by
        simpa only [map_add] using map_add_le_add p.seminorm (f.hom a) (f.hom b)
      map_one' := by simp only [map_one]
      map_mul' a b := by simp only [map_mul] }
  ultrametric a b := by
    change p.seminorm (f.hom (a + b)) ≤ _
    exact (congrArg p.seminorm (map_add f.hom a b)).le.trans
      (p.ultrametric (f.hom a) (f.hom b))
  extends_norm a := by
    change p.seminorm (f.hom (algebraMap K A a)) = ‖a‖
    rw [f.hom.commutes]
    exact p.extends_norm a
  bounded := by
    obtain ⟨cp, hcp, hp⟩ := p.bounded
    obtain ⟨cf, hcf, hf⟩ := f.bound
    refine ⟨cp * cf, mul_pos hcp hcf, fun a ↦ ?_⟩
    calc
      p.seminorm (f.hom a) ≤ cp * ‖f.hom a‖ := hp _
      _ ≤ cp * (cf * ‖a‖) := mul_le_mul_of_nonneg_left (hf a) hcp.le
      _ = (cp * cf) * ‖a‖ := (mul_assoc _ _ _).symm

theorem continuous_comapPoint (f : A ⟶ B) : Continuous (comapPoint f) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi fun a ↦ continuous_evaluation B (f.hom a)

def spectrumMap (f : A ⟶ B) : spectrum B ⟶ spectrum A :=
  TopCat.ofHom ⟨comapPoint f, continuous_comapPoint f⟩

@[simp]
theorem comapPoint_id (p : BoundedPoint A) : comapPoint (𝟙 A) p = p := by
  cases p
  dsimp [comapPoint]
  congr 1

@[simp]
theorem comapPoint_comp {C : AffinoidAlgebra K} (f : A ⟶ B) (g : B ⟶ C)
    (p : BoundedPoint C) : comapPoint (f ≫ g) p =
      comapPoint f (comapPoint g p) := by
  cases p
  dsimp [comapPoint]
  congr 1

/-- The actual contravariant weak-spectrum functor. -/
def spectrumFunctor : (AffinoidAlgebra K)ᵒᵖ ⥤ TopCat where
  obj A := spectrum A.unop
  map f := spectrumMap f.unop
  map_id A := by ext p; exact comapPoint_id p
  map_comp f g := by ext p; exact comapPoint_comp g.unop f.unop p

end MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
