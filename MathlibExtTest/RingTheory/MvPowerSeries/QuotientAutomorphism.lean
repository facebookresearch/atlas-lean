/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.QuotientAutomorphism

@[expose] public section

open MvPowerSeries

/-- `exactSource`: the original statement, with its original `Type` binders,
is exactly the public theorem. -/
private theorem exactSource
    (W₀ W : Type) [CommRing W₀] [IsNoetherianRing W₀] [CommRing W] [IsNoetherianRing W]
    (ψ : W₀ →+* W) (g₀ : MvPowerSeries (Fin 2) W₀) (g : MvPowerSeries (Fin 2) W)
    (hg : Ideal.span {g} = Ideal.span {MvPowerSeries.map ψ g₀})
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) ≃+*
      (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}))
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)
    (hθ₀C : ∀ w : W₀, θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (C w)) =
      Ideal.Quotient.mk (Ideal.span {g₀}) (C w))
    (hθ₀X : ∀ jj : Fin 2,
      θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (X jj)) -
          Ideal.Quotient.mk (Ideal.span {g₀}) (∑ ii : Fin 2, C (M₀ ii jj) * X ii) ∈
        (Ideal.span {Ideal.Quotient.mk (Ideal.span {g₀}) (X 0 : MvPowerSeries (Fin 2) W₀),
          Ideal.Quotient.mk (Ideal.span {g₀}) (X 1)}) ^ 2) :
    let S₀ := MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}
    let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {g₀})
    let S := MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {g})
    ∃ θ : S ≃+* S,
      (∀ w : W, θ (mkS (C w)) = mkS (C w)) ∧
      (∀ s s' : MvPowerSeries (Fin 2) W₀, θ₀ (mkS₀ s) = mkS₀ s' →
        θ (mkS (MvPowerSeries.map ψ s)) = mkS (MvPowerSeries.map ψ s')) ∧
      (∀ jj : Fin 2,
        θ (mkS (X jj)) - mkS (∑ ii : Fin 2, C (ψ (M₀ ii jj)) * X ii) ∈
          (Ideal.span {mkS (X 0), mkS (X 1)}) ^ 2) :=
  MvPowerSeries.exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq
    W₀ W ψ g₀ g hg θ₀ M₀ hθ₀C hθ₀X

/-- Higher-universe consumer: the public theorem is universe-polymorphic. -/
example
    (W₀ W : Type 1) [CommRing W₀] [IsNoetherianRing W₀] [CommRing W] [IsNoetherianRing W]
    (ψ : W₀ →+* W) (g₀ : MvPowerSeries (Fin 2) W₀) (g : MvPowerSeries (Fin 2) W)
    (hg : Ideal.span {g} = Ideal.span {MvPowerSeries.map ψ g₀})
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) ≃+*
      (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}))
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)
    (hθ₀C : ∀ w : W₀, θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (C w)) =
      Ideal.Quotient.mk (Ideal.span {g₀}) (C w))
    (hθ₀X : ∀ jj : Fin 2,
      θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (X jj)) -
          Ideal.Quotient.mk (Ideal.span {g₀}) (∑ ii : Fin 2, C (M₀ ii jj) * X ii) ∈
        (Ideal.span {Ideal.Quotient.mk (Ideal.span {g₀}) (X 0 : MvPowerSeries (Fin 2) W₀),
          Ideal.Quotient.mk (Ideal.span {g₀}) (X 1)}) ^ 2) :
    ∃ θ : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) ≃+*
        (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}),
      ∀ w : W, θ (Ideal.Quotient.mk (Ideal.span {g}) (C w)) =
        Ideal.Quotient.mk (Ideal.span {g}) (C w) := by
  obtain ⟨θ, hC, -, -⟩ :=
    MvPowerSeries.exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq
      W₀ W ψ g₀ g hg θ₀ M₀ hθ₀C hθ₀X
  exact ⟨θ, hC⟩
