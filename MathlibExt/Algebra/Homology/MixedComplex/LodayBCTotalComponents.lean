/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.MixedComplex.LodayBCCoordinateLaws

/-!
# Both actual total components in the printed BC coordinates

The full bicomplex coordinate isomorphism transports horizontal and vertical
total components separately. The printed arrows commute as column chain maps;
its native totalization inserts epsilon(p) in the vertical component, giving
the actual anti-commuting pair. This retains the original b and B through the
full coordinate comparison, not through a degreewise B-only replacement.
-/

@[expose] public section
noncomputable section

open CategoryTheory HomologicalComplex HomologicalComplex₂

universe u v

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasFiniteCoproducts C]
  (M : MixedComplex C)

/-- The actual original horizontal total component is transported by the full BC coordinate map. -/
theorem lodayBCTotalIso_D₁ (i j : ℕ) :
    M.lodayBCTotalIso.hom.f i ≫ M.connesBicomplex.D₁ (ComplexShape.down ℕ) i j =
      M.lodayBCBicomplex.D₁ (ComplexShape.down ℕ) i j ≫ M.lodayBCTotalIso.hom.f j :=
  HomologicalComplex₂.total.mapAux.mapMap_D₁
    (K := M.lodayBCBicomplex) (L := M.connesBicomplex) (φ := M.lodayBCBicomplexIso.hom)
    (c₁₂ := ComplexShape.down ℕ) i j

/-- The actual original vertical total component, including epsilon(p), is transported by the same full map. -/
theorem lodayBCTotalIso_D₂ (i j : ℕ) :
    M.lodayBCTotalIso.hom.f i ≫ M.connesBicomplex.D₂ (ComplexShape.down ℕ) i j =
      M.lodayBCBicomplex.D₂ (ComplexShape.down ℕ) i j ≫ M.lodayBCTotalIso.hom.f j :=
  HomologicalComplex₂.total.mapAux.mapMap_D₂
    (K := M.lodayBCBicomplex) (L := M.connesBicomplex) (φ := M.lodayBCBicomplexIso.hom)
    (c₁₂ := ComplexShape.down ℕ) i j

/-- The printed total's actual horizontal/vertical components satisfy the native anti-commutation law. -/
theorem lodayBCTotal_D₁_D₂ (i j k : ℕ) :
    M.lodayBCBicomplex.D₁ (ComplexShape.down ℕ) i j ≫ M.lodayBCBicomplex.D₂ (ComplexShape.down ℕ) j k +
      M.lodayBCBicomplex.D₂ (ComplexShape.down ℕ) i j ≫ M.lodayBCBicomplex.D₁ (ComplexShape.down ℕ) j k = 0 := by
  rw [M.lodayBCBicomplex.D₁_D₂]
  exact neg_add_cancel _

/-- The literal BC arrow model has the same actual total homology as the original mixed Connes model. -/
def lodayBCTotalHomologyIso (n : ℕ)
    [(M.lodayBCBicomplex.total (ComplexShape.down ℕ)).HasHomology n]
    [(M.connesBicomplex.total (ComplexShape.down ℕ)).HasHomology n] :
    (M.lodayBCBicomplex.total (ComplexShape.down ℕ)).homology n ≅
      (M.connesBicomplex.total (ComplexShape.down ℕ)).homology n :=
  HomologicalComplex.homologyMapIso M.lodayBCTotalIso n

end MixedComplex
