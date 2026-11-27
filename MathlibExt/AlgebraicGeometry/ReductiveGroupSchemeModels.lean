/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The geometric reductivity formulation adapts The Tau Ceti contributors,
TauCetiProject/TauCeti, revision62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/Algebra/AlgebraicGroup/Reductive/Basic.lean and
TauCeti/AlgebraicGeometry/AffineGroupScheme/Reductive/Basic.lean,
released under Apache2.0 in that repository's LICENSE.
Modifications: express the same geometric subgroup condition on native
scheme slices; express unipotence by a faithful regular representation
into actual unitriangular matrices on every scheme-valued test. The
completed source equivalence with the coordinate-Hopf predicate is a
separate integration dictionary, not a new requested theorem.
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import MathlibExt.AlgebraicGeometry.AbelianSchemes

/-!
# Actual geometric reductive group-scheme contracts

All group objects are native schemes over an arbitrary base. A regular
linear representation is a natural family on all test schemes with
matrix coefficients pulled back by actual regular-section maps. This
retains nonreduced tests and characterizes a regular group morphism.
Unipotence means a faithful unitriangular representation; normality uses
the actual pointwise conjugation on every test scheme. Reductivity then
excludes connected normal smooth unipotent closed subgroups in every
algebraically closed geometric fibre.

This is the standard geometric definition, not linear reductivity.
Reference: Conrad, *Reductive group schemes*, Section3. The coordinate
formulation and its proof are already present in the cited Tau source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonObj _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

variable (k : Type) [Field k]
  (H : Over (Spec (.of k))) [GrpObj H]

/-- A regular representation, normalized on all actual scheme-valued points. -/
structure LinearRepresentation (n : ℕ) where
  map : ∀ T : Over (Spec (.of k)),
    (T ⟶ H) →* Matrix.GeneralLinearGroup (Fin n) Γ(T.left, ⊤)
  naturality : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U)
    (h : U ⟶ H) (i j : Fin n),
    (map T (f ≫ h) : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j =
      f.left.appTop ((map U h : Matrix (Fin n) (Fin n) Γ(U.left, ⊤)) i j)

/-- The actual unitriangular condition on every matrix coefficient. -/
def IsUnitriangular {n : ℕ} (ρ : LinearRepresentation k H n) : Prop :=
  ∀ (T : Over (Spec (.of k))) (h : T ⟶ H) (i j : Fin n),
    j ≤ i → (ρ.map T h : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j =
      if i = j then 1 else 0

/-- A faithful regular unitriangular representation of the actual group. -/
def IsUnipotent : Prop :=
  ∃ (n : ℕ) (ρ : LinearRepresentation k H n),
    (∀ T, Function.Injective (ρ.map T)) ∧ IsUnitriangular k H ρ

variable {k H}

/-- Scheme-theoretic normality, via all actual test-scheme conjugations. -/
def IsNormalSubgroup {G : Over (Spec (.of k))} [GrpObj G]
    (i : H ⟶ G) [IsMonHom i] : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : T ⟶ G) (h : T ⟶ H),
    ∃ h' : T ⟶ H, h' ≫ i = g * (h ≫ i) * g⁻¹

variable (S : Scheme.{0}) (G : Over S) [GrpObj G]

/-- No nontrivial connected normal smooth unipotent subgroup in any fibre. -/
def HasReductiveGeometricFibres : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (H : Over (Spec (.of Ω))) [GrpObj H] [IsAffineHom H.hom]
    [LocallyOfFinitePresentation H.hom] [Smooth H.hom]
    [GeometricallyConnected H.hom]
    (i : H ⟶ (Over.pullback s).obj G) [IsMonHom i]
    [IsClosedImmersion i.left],
      IsNormalSubgroup i → IsUnipotent Ω H → Nonempty (H ≅ 𝟙_ (Over (Spec (.of Ω))))

/-- A native reductive group scheme over an arbitrary actual base. -/
class IsReductive : Prop where
  [affine : IsAffineHom G.hom]
  [presentation : LocallyOfFinitePresentation G.hom]
  [smooth : Smooth G.hom]
  [connected : GeometricallyConnected G.hom]
  geometric : HasReductiveGeometricFibres S G

attribute [instance] IsReductive.affine IsReductive.presentation
  IsReductive.smooth IsReductive.connected

end MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
