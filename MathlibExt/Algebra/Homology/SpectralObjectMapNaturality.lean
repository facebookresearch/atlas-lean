/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectMap

public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Interchange of spectral-object maps and interval-diagram maps

Let X,Y be spectral objects in an abelian category C indexed by an arbitrary category ι, and
φ:X→Y a morphism of spectral objects. A morphism α between composable three-arrow diagrams f and
g induces maps between their defining spectral short complexes. For degrees n₀+1=n₁ and n₁+1=n₂,
the short complex has terms H^{n₀}(f₃)→H^{n₁}(f₂)→H^{n₂}(f₁), with the connecting arrows of the
spectral object.

The interval-diagram map and the map induced by φ commute on these short complexes:
S_X(α)≫S_φ(g)=S_φ(f)≫S_Y(α). Passing to short-complex homology gives the same interchange
equation for the E-objects, E_X(α)≫E_φ(g)=E_φ(f)≫E_Y(α). The category, morphism and
index-category universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComposableArrows

universe v u vι uι

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y : SpectralObject C ι}

namespace Hom

/-- Let C be abelian, ι any category, X,Y spectral objects in C indexed by ι, and φ:X→Y. Let
f=(f₁,f₂,f₃) and g=(g₁,g₂,g₃) be composable three-arrow diagrams in ι and α:f→g a morphism of
those diagrams. Choose integers n₀,n₁,n₂ with n₀+1=n₁ and n₁+1=n₂. Write S_X(f) for
H^{n₀}_X(f₃)→H^{n₁}_X(f₂)→H^{n₂}_X(f₁), with its connecting arrows, and similarly for Y and g.
Let S_X(α),S_Y(α) be the diagram-induced short-complex maps and S_φ(f),S_φ(g) the maps with
components φ in the three respective degrees. Then S_X(α)≫S_φ(g)=S_φ(f)≫S_Y(α). -/
@[reassoc]
theorem shortComplexMap_naturality
    (phi : X ⟶ Y)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ ≫
        shortComplexMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂ =
      shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  apply ShortComplex.Hom.ext
  · exact (phi.hom n₀).naturality _
  · exact (phi.hom n₁).naturality _
  · exact (phi.hom n₂).naturality _

/-- Let C be abelian, ι any category, X,Y spectral objects in C indexed by ι, and φ:X→Y. Let
f=(f₁,f₂,f₃) and g=(g₁,g₂,g₃) be composable three-arrow diagrams in ι and α:f→g a morphism of
those diagrams. Choose integers n₀,n₁,n₂ with n₀+1=n₁ and n₁+1=n₂. For the associated E-objects,
let E_X(α):E_X(f)→E_X(g) and E_Y(α) be induced by α, while E_φ(f):E_X(f)→E_Y(f) and E_φ(g) are
induced by φ. Then E_X(α)≫E_φ(g)=E_φ(f)≫E_Y(α). All four maps are the homology maps of the
corresponding defining short-complex maps in degrees n₀,n₁,n₂. -/
@[reassoc]
theorem map_EMap
    (phi : X ⟶ Y)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ ≫
        EMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂ =
      EMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  change ShortComplex.homologyMap
        (X.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂) ≫
      ShortComplex.homologyMap
        (shortComplexMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂) =
    ShortComplex.homologyMap
        (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      ShortComplex.homologyMap
        (Y.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂)
  exact ShortComplex.homologyMap_square
    (shortComplexMap_naturality phi f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂)

end Hom

end CategoryTheory.Abelian.SpectralObject

end
