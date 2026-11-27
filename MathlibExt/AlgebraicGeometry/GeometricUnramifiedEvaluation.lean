/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleCorestriction
public import MathlibExt.AlgebraicGeometry.LogPairs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Actual unramified torsion classes and local evaluations

Unramified classes are actual field cohomology classes extending across
every geometric discrete-valuation subalgebra (with the given fraction field)
containing the base field. These
are images of the fixed native restriction maps, not a freely named
unramified group. Local lift data live in the actual stalk ring's
small-étale cohomology and restrict to the given field class.

Evaluation is restriction of that same local lift to the actual residue
field. Independence uses injectivity of that actual local-to-generic map.
The Gersten/local-extension comparison is the remaining construction
boundary; no evaluation value or residue-field map is an oracle.

Source: Schreieder arXiv1801.05397v5, §2.3 and Proposition 3.1;
Bloch--Ogus purity/Gersten comparison. Generic local rings, scheme
residue maps and étale functoriality are positively reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open MathlibExt.AlgebraicGeometry.LogPairs

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

/-- The actual generic map of a discrete-valuation subalgebra of the given field. -/
abbrev dvrGenericMap {k K : Type} [Field k] [Field K] [Algebra k K] (A : Subalgebra k K) :
    Spec (.of K) ⟶ Spec (.of A) := Spec.algebraMap A K

/-- A discrete valuation ring `A ⊆ K` of the field `K ⊇ k` (with fraction field `K`) is
geometric over `k` if its residue field has transcendence degree over `k` one less than
that of `K` (Schreieder, §2.3): for a finitely generated function field these are the
valuations of prime divisors on normal models. -/
def IsGeometricDVR {k K : Type} [Field k] [Field K] [Algebra k K] (A : Subalgebra k K)
    [IsDiscreteValuationRing A] [IsFractionRing A K] : Prop :=
  Algebra.trdeg k (IsLocalRing.ResidueField A) + 1 = Algebra.trdeg k K

/-- A class $a ∈ H^i(K, μ_l^{⊗ j})$ of a field $K ⊇ k$, in the cohomology system `S`, is unramified
if for every geometric discrete valuation subalgebra $A$ of $K$ containing $k$, with fraction field
$K$, $a$ is the restriction of a class in $H^i(\operatorname{Spec} A, μ_l^{⊗ j})$ (Schreieder,
§2.3). Here $l$ is a natural number invertible in $k$ (hypothesis `hl`). -/
def IsUnramified {l : ℕ} (S : System l) (k K : Type) [Field k] [Field K] [Algebra k K]
    (_hl : IsUnit (l : k)) (i : ℤ) (j : ℕ) (a : S.toData.H (Spec (.of K)) i j) : Prop :=
  ∀ (A : Subalgebra k K) [IsDiscreteValuationRing A] [IsFractionRing A K],
    IsGeometricDVR A → ∃ b : S.toData.H (Spec (.of A)) i j,
      S.toData.restriction (dvrGenericMap A) i j b = a

/-- The actual subgroup of field classes extending over all geometric DVRs. -/
def unramifiedSubgroup {l : ℕ} (S : System l) (k K : Type) [Field k] [Field K] [Algebra k K]
    (hl : IsUnit (l : k)) (i : ℤ) (j : ℕ) : AddSubgroup (S.toData.H (Spec (.of K)) i j) where
  carrier := {a | IsUnramified S k K hl i j a}
  zero_mem' := by
    change IsUnramified S k K hl i j 0
    intro A _ _ _
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro a b ha hb
    change IsUnramified S k K hl i j a at ha
    change IsUnramified S k K hl i j b at hb
    change IsUnramified S k K hl i j (a + b)
    intro A _ _ hA
    obtain ⟨a', ha'⟩ := ha A hA
    obtain ⟨b', hb'⟩ := hb A hA
    exact ⟨a' + b', by rw [map_add, ha', hb']⟩
  neg_mem' := by
    intro a ha
    change IsUnramified S k K hl i j a at ha
    change IsUnramified S k K hl i j (-a)
    intro A _ _ hA
    obtain ⟨a', ha'⟩ := ha A hA
    exact ⟨-a', by rw [map_neg, ha']⟩

variable {k : Type} [Field k] {n : ℕ}

/-- Unramified subgroup for the variety's actual generic-point function field. -/
def varietyUnramified {l : ℕ} (S : System l) (V : NormalVariety k n) (hl : IsUnit (l : k))
    (i : ℤ) (j : ℕ) : AddSubgroup (S.toData.H (Spec (.of (FunctionField V))) i j) := by
  letI := fractionAlgebra V
  exact unramifiedSubgroup S k (FunctionField V) hl i j

def localGenericMap (V : NormalVariety k n) (x : V.X.left) :
    Spec (.of (FunctionField V)) ⟶ Spec (.of (LocalRing V x)) :=
  Spec.map (CommRingCat.ofHom (localToField V x))

def localResidueMap (V : NormalVariety k n) (x : V.X.left) :
    Spec (.of (IsLocalRing.ResidueField (LocalRing V x))) ⟶ Spec (.of (LocalRing V x)) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (LocalRing V x)))

/-- A local class in the actual stalk ring which restricts to the given field class. -/
structure LocalLift {l : ℕ} (S : System l) (V : NormalVariety k n) (hl : IsUnit (l : k))
    (i : ℤ) (j : ℕ)
    (a : varietyUnramified S V hl i j) (x : V.X.left) where
  value : S.toData.H (Spec (.of (LocalRing V x))) i j
  normalized : S.toData.restriction (localGenericMap V x) i j value = a.val

/-- Gersten comparison data: all actual local lifts, with the actual restriction injectivity. -/
structure LocalEvaluationData {l : ℕ} (S : System l) (V : NormalVariety k n)
    (hl : IsUnit (l : k)) (i : ℤ) (j : ℕ) (a : varietyUnramified S V hl i j) where
  lift : ∀ x : V.X.left, LocalLift S V hl i j a x
  injective : ∀ x : V.X.left,
    Function.Injective (S.toData.restriction (localGenericMap V x) i j)

/-- Evaluation is the literal residue-field restriction of the chosen actual local lift. -/
def LocalEvaluationData.evaluate {l : ℕ} {S : System l} {V : NormalVariety k n}
    {hl : IsUnit (l : k)} {i : ℤ} {j : ℕ} {a : varietyUnramified S V hl i j}
    (D : LocalEvaluationData S V hl i j a) (x : V.X.left) :
    S.toData.H (Spec (.of (IsLocalRing.ResidueField (LocalRing V x)))) i j :=
  S.toData.restriction (localResidueMap V x) i j (D.lift x).value

/-- Actual local restriction injectivity makes evaluation independent of every lift choice. -/
theorem evaluation_independent {l : ℕ} {S : System l} {V : NormalVariety k n}
    {hl : IsUnit (l : k)} {i : ℤ} {j : ℕ} {a : varietyUnramified S V hl i j}
    (D E : LocalEvaluationData S V hl i j a) (x : V.X.left) :
    D.evaluate x = E.evaluate x := by
  have h : (D.lift x).value = (E.lift x).value :=
    D.injective x ((D.lift x).normalized.trans (E.lift x).normalized.symm)
  exact congrArg (S.toData.restriction (localResidueMap V x) i j) h


/-- Pointwise evaluation also applies on the smooth locus of a singular ambient variety. -/
def LocalLift.evaluate {l : ℕ} {S : System l} {V : NormalVariety k n}
    {hl : IsUnit (l : k)} {i : ℤ} {j : ℕ} {a : varietyUnramified S V hl i j} {x : V.X.left}
    (L : LocalLift S V hl i j a x) :
    S.toData.H (Spec (.of (IsLocalRing.ResidueField (LocalRing V x)))) i j :=
  S.toData.restriction (localResidueMap V x) i j L.value

theorem local_evaluation_independent {l : ℕ} {S : System l} {V : NormalVariety k n}
    {hl : IsUnit (l : k)} {i : ℤ} {j : ℕ} {a : varietyUnramified S V hl i j} {x : V.X.left}
    (L M : LocalLift S V hl i j a x)
    (h : Function.Injective (S.toData.restriction (localGenericMap V x) i j)) :
    L.evaluate = M.evaluate :=
  congrArg (S.toData.restriction (localResidueMap V x) i j)
    (h (L.normalized.trans M.normalized.symm))


/-- Ordinary pointwise-to-global constructor on the actual local lift/injectivity family. -/
def LocalEvaluationData.ofPointwise {l : ℕ} {S : System l} {V : NormalVariety k n}
    {hl : IsUnit (l : k)} {i : ℤ} {j : ℕ} {a : varietyUnramified S V hl i j}
    (L : ∀ x : V.X.left,
      {_P : LocalLift S V hl i j a x //
        Function.Injective (S.toData.restriction (localGenericMap V x) i j)}) :
    LocalEvaluationData S V hl i j a where
  lift x := (L x).val
  injective x := (L x).property

end MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation
