/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EtaleNilpotentLifting

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

-- Consumer with the original binders (`Scheme.{0}`).
example {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q] (k : T₀ ⟶ T)
    [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ :=
  AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker q k hk t s₀ hs₀

-- Higher-universe consumer (`Scheme.{1}`).
example {X Y T T₀ : Scheme.{1}} (q : Y ⟶ X) [Etale q] (k : T₀ ⟶ T)
    [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ :=
  AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker q k hk t s₀ hs₀

