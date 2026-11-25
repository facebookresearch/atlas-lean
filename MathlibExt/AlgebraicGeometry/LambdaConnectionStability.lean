/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFramedLambdaFamilies
public import MathlibExt.AlgebraicGeometry.RationalChernZeroHiggsBundles

/-!
# Actual invariant-subsheaf stability of lambda-connections

An invariant subsheaf is preserved by the literal connection operator on
every open, through the actual sheafified tensor inclusion. It is not an
arbitrary subsheaf of the underlying vector bundle. Semistability uses the
same coherent torsion-free, saturated, positive generic-rank slope tests as
the Higgs interface, with the actual cohomology-normalized Hilbert data.
This definition applies at nonzero lambda as well as at zero. On an
integral zero-dimensional smooth projective variety, every positive-rank
bundle is semistable, and stability means rank one.

The zero Higgs object is the existing actual zero-operator functor. Its
stability comparison is a separate target. There is no free Higgs field,
Chern-class assignment or stability theorem supplied in these definitions.

Source: Simpson, alg-geom/9604005v1, Theorem 2.3, Proposition 4.1 and
the cited Lambda-module stability construction. The actual differential,
tensor, Hilbert and source coefficient primitives retain their revision,
author and Apache license notices in the imported modules.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

  AlgebraicGeometry.SheafedSpace.sheaf

namespace MathlibExt.AlgebraicGeometry.LambdaConnectionStability

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open RelativeDifferentialForms RelativeDeRhamDifferential AlgebraicLambdaConnections
open AlgebraicLineBundleFamilies LineBundleTaskContracts PolarizedHiggsStability
open NumericalCompactifiedJacobians ProjectiveLineSystems

variable {X : PerverseSheaves.ComplexScheme} {T : Scheme.{0}} {pi : X.left ⟶ T}
  {lambda : Γ(T, ⊤)} {D : Differential pi}

def IsInvariant (N : LambdaConnection pi lambda D) (F : X.left.Modules)
    (i : F ⟶ N.object) : Prop :=
  ∀ (U : X.left.Opens) (s : F.val.obj (op U)),
    ∃ t : (moduleTensor X.left F (forms pi 1)).val.obj (op U),
      ((tensorMap i (𝟙 (forms pi 1))).val.app (op U)).hom t =
        N.nabla0 U ((i.val.app (op U)).hom s)

structure CoherentConnection (pi : X.left ⟶ T) (lambda : Γ(T, ⊤)) (D : Differential pi) where
  connection : LambdaConnection pi lambda D
  coherent : IsFiniteTypeQuasicoherent connection.object

def IsSemistable {H : LineBundle X.left} {d : ℕ} (P : HilbertNumerics X H d)
    (E : CoherentConnection pi lambda D) : Prop :=
  0 < E.connection.rank ∧ (d = 0 ∨
    ∀ (F : X.left.Modules) (hF : IsFiniteTypeQuasicoherent F) (r : ℕ),
      0 < r → r < E.connection.rank → HasGenericRank F r → IsTorsionFree F →
        ∀ i : F ⟶ E.connection.object, Mono i → IsTorsionFree (cokernel i) →
          IsInvariant E.connection F i →
            slope P F hF r ≤ slope P E.connection.object E.coherent E.connection.rank)

def IsStable {H : LineBundle X.left} {d : ℕ} (P : HilbertNumerics X H d)
    (E : CoherentConnection pi lambda D) : Prop :=
  0 < E.connection.rank ∧ ((d = 0 ∧ E.connection.rank = 1) ∨
    (0 < d ∧ ∀ (F : X.left.Modules) (hF : IsFiniteTypeQuasicoherent F) (r : ℕ),
      0 < r → r < E.connection.rank → HasGenericRank F r → IsTorsionFree F →
        ∀ i : F ⟶ E.connection.object, Mono i → IsTorsionFree (cokernel i) →
          IsInvariant E.connection F i →
            slope P F hF r < slope P E.connection.object E.coherent E.connection.rank))

theorem isSemistable_dimension_zero {H : LineBundle X.left}
    (P : HilbertNumerics X H 0) (E : CoherentConnection pi lambda D) :
    IsSemistable P E ↔ 0 < E.connection.rank := by
  simp [IsSemistable]

theorem isStable_dimension_zero {H : LineBundle X.left}
    (P : HilbertNumerics X H 0) (E : CoherentConnection pi lambda D) :
    IsStable P E ↔ E.connection.rank = 1 := by
  simp only [IsStable, Nat.lt_irrefl, false_and, or_false, true_and]
  constructor
  · exact fun h ↦ h.2
  · intro h
    rw [h]
    exact ⟨Nat.zero_lt_one, rfl⟩

variable {D : Differential X.hom}

def zeroCoherent (C : LambdaZeroHiggsComparison.AbsoluteFormsComparison X)
    (E : CoherentConnection X.hom 0 D) : PolarizedHiggsStability.CoherentBundle X where
  bundle := LambdaZeroHiggsComparison.zeroHiggs C E.connection
  coherent := E.coherent

end MathlibExt.AlgebraicGeometry.LambdaConnectionStability
