/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Geometry 609, Geometry 610

open Manifold

/-!
# Christoffel symbols; Levi-Civita connection

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)

## References

* https://en.wikipedia.org/wiki/Christoffel_symbols (for `christoffelSymbols`)
* https://en.wikipedia.org/wiki/Levi-Civita_connection (for `leviCivitaConnection`)
-/

namespace MetaMathlibExt

-- Geometry 609: Christoffel symbols

/-- Let g: ℝⁿ → Mₙ(ℝ), where Mₙ(ℝ) denotes the space of n× n matrices. The Christoffel symbols are
Γᵢⱼᵏ=1/2 gᵏˡ( g_{jl,i}+ g_{li,j}-g_{ij,l}) where i,j,k,l∈ {1, ⋯, n} and we use Einstein's summation
convention.
-/
noncomputable def christoffelSymbols
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n)) (k i j : Fin n) : ℝ :=
  let e := fun s : Fin n => EuclideanSpace.single s (1 : ℝ)
  let d := fun a b c => fderiv ℝ (fun q => (g q) b c) p (e a)
  let gInv := (g p)⁻¹
  (1/2 : ℝ) * ∑ l : Fin n, gInv k l * (d i j l + d j i l - d l i j)

-- Geometry 610: Levi-Civita connection

noncomputable def christoffelConnection
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  ∑ k : Fin n, christoffelSymbols g p k i j • EuclideanSpace.single k (1 : ℝ)

noncomputable def leviCivitaConnectionChart
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n))
    (X Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ Y p (X p) + ∑ i : Fin n, ∑ j : Fin n,
    (X p i * Y p j) • christoffelConnection g p i j

/-- Let (M,g) be a Riemannian manifold, {∂ᵢ}ᵢ₌₁ⁿ a local coordinate basis and Γᵢⱼᵏ the Christoffel
symbols, then the Levi-Civita connection is defined by ∇_{∂ᵢ} ∂ⱼ = Γᵢⱼᵏ ∂ ₖ which by linearity and
Leibnitz rule extends to vector fields X,Y to give us (∇_X Y)ᵏ = ∑ᵢ Xⁱ ∂ᵢ Yᵏ + ∑_{i,j} Γᵏᵢⱼ Xⁱ Yʲ.
-/
noncomputable def leviCivitaConnection
    {M : Type*} [TopologicalSpace M] {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : ℕ∞) M]
    (e : PartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (W Z : ∀ q : M, TangentSpace (𝓡 n) q)
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) :
    ∀ q : M, TangentSpace (𝓡 n) q :=
  fun p =>
    let Wc := fun y => (W (e.symm y) : EuclideanSpace ℝ (Fin n))
    let Zc := fun y => (Z (e.symm y) : EuclideanSpace ℝ (Fin n))
    (leviCivitaConnectionChart g (e p) Wc Zc : EuclideanSpace ℝ (Fin n))

end MetaMathlibExt

end
