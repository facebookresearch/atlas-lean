/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual vector bundles, degrees and slopes on curves

Local trivializations use finite coproducts of the structure sheaf. On a
proper curve (`IsProperCurve`), the degree of a vector bundle `E` of rank
`r` is `χ(E) - r χ(𝒪)`: its actual Euler characteristic minus `r` times
that of the structure sheaf. The slope of a vector bundle of positive rank
is its degree divided by its rank. Degree and slope take the witness
`IsVectorBundle E r` that ties `r` to `E`, and slope also takes `0 < r`.
On invertible sheaves the degree is `CoherentCurveLinearSeries.degree`.
Global generation is the existence of a family of generating global
sections, Mathlib's `SheafOfModules.GeneratingSections`.

References: Stacks Project, Tag 0AYR (degree of a locally free sheaf on a
proper curve); Huybrechts–Lehn, *The Geometry of Moduli Spaces of Sheaves*,
Chapter 1, https://doi.org/10.1017/CBO9780511711985.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CurveVectorBundles

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- The trivial bundle of rank `r`: a coproduct of `r` copies of the structure
sheaf. -/
def trivialBundle (X : Scheme.{u}) (r : ℕ) : X.Modules :=
  ∐ fun _ : Fin r ↦ structureModule X

/-- Local triviality of rank `r`, on actual Zariski open subschemes. -/
def IsVectorBundle {X : Scheme.{u}} (E : X.Modules) (r : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅ trivialBundle U r)

/-- The trivial bundle of rank zero is the zero module. -/
theorem isZero_trivialBundle_zero (X : Scheme.{u}) : IsZero (trivialBundle X 0) := by
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ (fun i ↦ Fin.elim0 i)

/-- Every section of a module over an open contained in an open where its restriction vanishes
is zero. -/
theorem section_eq_zero_of_isZero_pullback {X : Scheme.{u}} {E : X.Modules} {V : X.Opens}
    (hV : IsZero ((Scheme.Modules.pullback V.ι).obj E)) {W : X.Opens} (hW : W ≤ V)
    (t : Γ(E, W)) : t = 0 := by
  have hR : IsZero (E.restrict V.ι) :=
    hV.of_iso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app E)
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hW
  revert t
  rw [← himg]
  intro t
  have h0 : ∀ s : Γ(E.restrict V.ι, V.ι ⁻¹ᵁ W), s = 0 := fun s ↦ by
    have := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (V.ι ⁻¹ᵁ W) s) (hR.eq_of_src (𝟙 _) 0)
    simpa using this
  have h1 := h0 ((Scheme.Modules.restrictAppIso V.ι E (V.ι ⁻¹ᵁ W)).inv t)
  calc t = (Scheme.Modules.restrictAppIso V.ι E (V.ι ⁻¹ᵁ W)).hom
        ((Scheme.Modules.restrictAppIso V.ι E (V.ι ⁻¹ᵁ W)).inv t) := by simp
    _ = 0 := by rw [h1, map_zero]

/-- A vector bundle of rank zero is the zero module. -/
theorem isZero_of_isVectorBundle_zero {X : Scheme.{u}} {E : X.Modules}
    (h : IsVectorBundle E 0) : IsZero E := by
  rw [IsZero.iff_id_eq_zero]
  ext U s
  suffices hs : s = 0 by simpa using hs
  refine TopCat.Presheaf.section_ext ⟨E.presheaf, E.isSheaf⟩ U s 0 (fun x hx ↦ ?_)
  obtain ⟨V, hxV, ⟨e⟩⟩ := h x
  have hV : IsZero ((Scheme.Modules.pullback V.ι).obj E) :=
    (isZero_trivialBundle_zero V).of_iso e
  have hres := section_eq_zero_of_isZero_pullback hV (inf_le_right : U ⊓ V ≤ V)
    (E.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)
  change E.presheaf.germ U x hx s = E.presheaf.germ U x hx 0
  rw [← TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE (inf_le_left : U ⊓ V ≤ U)) x
    (TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hxV⟩), hres, map_zero, map_zero]

/-- The trivial bundle of rank one is the structure sheaf. -/
def trivialBundleOneIso (X : Scheme.{u}) : trivialBundle X 1 ≅ structureModule X :=
  coproductUniqueIso _

/-- The vector bundles of rank one are exactly the invertible sheaves. -/
theorem isVectorBundle_one_iff {X : Scheme.{u}} (L : X.Modules) :
    IsVectorBundle L 1 ↔ IsLineBundle L := by
  constructor
  · intro h x
    obtain ⟨U, hx, ⟨e⟩⟩ := h x
    exact ⟨U, hx, ⟨e ≪≫ trivialBundleOneIso U⟩⟩
  · intro h x
    obtain ⟨U, hx, ⟨e⟩⟩ := h x
    exact ⟨U, hx, ⟨e ≪≫ (trivialBundleOneIso U).symm⟩⟩

/-- The degree `χ(E) - r χ(𝒪_X)` of a vector bundle `E` of rank `r` on a proper
curve (Stacks, Tag 0AYR). Cohomology vanishes above degree one and the
cohomology of a vector bundle on a proper curve is finite-dimensional, so
`χ = h⁰ - h¹` with actual dimensions. -/
def bundleDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (E : X.Modules) (r : ℕ)
    (_hE : IsVectorBundle E r) : ℤ :=
  (Module.finrank k (cohomology f E 0) : ℤ) -
    Module.finrank k (cohomology f E 1) - (r : ℤ) *
      ((Module.finrank k (cohomology f (structureModule X) 0) : ℤ) -
        Module.finrank k (cohomology f (structureModule X) 1))

/-- On an invertible sheaf, the degree of a rank-one bundle is the line-bundle
degree `χ(L) - χ(𝒪_X)`. -/
theorem bundleDegree_eq_degree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (L : X.Modules)
    (hE : IsVectorBundle L 1) (hL : IsLineBundle L) :
    bundleDegree f L 1 hE = degree f L hL := by
  simp only [bundleDegree, degree, Nat.cast_one, one_mul]
  ring

/-- The slope `deg(E) / r` of a vector bundle `E` of positive rank `r` on a proper
curve. -/
def slope {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (E : X.Modules) (r : ℕ)
    (hE : IsVectorBundle E r) (_hr : 0 < r) : ℚ :=
  (bundleDegree f E r hE : ℚ) / r

/-- The condition that a sheaf of `𝒪_X`-modules `E` is generated by global sections: there is a
(possibly infinite) family of global sections `(s_i)_{i ∈ I}` such that the induced morphism from
the free module `𝒪_X^{(I)}` to `E` is an epimorphism (`SheafOfModules.GeneratingSections`). -/
def GloballyGenerated {X : Scheme.{u}} (E : X.Modules) : Prop :=
  Nonempty (SheafOfModules.GeneratingSections (R := X.ringCatSheaf) E)

end MathlibExt.AlgebraicGeometry.CurveVectorBundles
