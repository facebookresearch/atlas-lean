/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.LocallyFreeOfRank

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- Consumer with the original binders. -/
example {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ e : Fin n → Γ(M, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
        ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) :=
  hM.exists_basis x

/-- On a locally free sheaf of rank `n`, the sections near any point have rank `n`. -/
example {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ Module.Free Γ(X, V) Γ(M, V) := by
  obtain ⟨V, hx, e, he⟩ := hM.exists_basis x
  obtain ⟨b, -⟩ := he V le_rfl
  exact ⟨V, hx, Module.Free.of_basis b⟩
