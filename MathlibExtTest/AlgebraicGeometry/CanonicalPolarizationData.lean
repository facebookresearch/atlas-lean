/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CanonicalPolarizationData

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor
open MathlibExt.AlgebraicGeometry.QMCanonicalPol

universe u v

namespace CanonicalPolarizationDataTest

/-- Consumer with the original binders: canonical polarization data gives
an invertible symmetric sheaf whose Mumford kernel is the `2`-torsion and
which is Rosati compatible. -/
theorem exactSource {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L) :
    IsLineBundle L ∧ IsSymmetric G L ∧
      KernelIsTwoTorsion G L ∧
      RosatiCompatible G L act act_over star :=
  ⟨h.isLineBundle, h.isSymmetric, h.kernelIsTwoTorsion,
    h.rosatiCompatible⟩

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 {S : Type 1} [CommRing S] {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type 1} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L) :
    IsLineBundle L ∧ IsSymmetric G L ∧
      KernelIsTwoTorsion G L ∧
      RosatiCompatible G L act act_over star :=
  ⟨h.isLineBundle, h.isSymmetric, h.kernelIsTwoTorsion,
    h.rosatiCompatible⟩

/-- The global-section rank on a fibre depends only on the structure
morphism `f`, not on the group law, and the positive-rank field states it
for `f`. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    0 < geomFibreH0Finrank f L k sk :=
  h.positiveRank k sk

/-- The canonical-form field needs no compatible law from outside: the base
change of `G` meets its compatibility hypothesis, so the field gives an
invertible sheaf that is kernel-trivial for that base change. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∃ L₀ : (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
        IsLineBundle L₀ ∧
        KernelTrivial
          (G.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₀ := by
  obtain ⟨S', _, _, hS', hform⟩ := h.locallyCanonicalForm
  obtain ⟨L₀, hL₀, hK, -⟩ :=
    hform (G.baseChange _) fun t' P Q ↦ baseChange_mul_left_fst G _ t' P Q
  exact ⟨S', _, _, hS', L₀, hL₀, hK⟩

/-- The same witness through `exists_baseChange_canonicalForm`. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∃ L₀ : (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
        IsLineBundle L₀ ∧
        KernelTrivial
          (G.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₀ := by
  obtain ⟨S', _, _, hS', L₀, hL₀, hK, -⟩ := h.exists_baseChange_canonicalForm
  exact ⟨S', _, _, hS', L₀, hL₀, hK⟩

/-- Boundary point: the identity point satisfies the `2`-torsion
equation in the kernel condition, and negation is over the base. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    G.mul t (G.one t) (G.one t) = G.one t ∧ negMor G ≫ f = f :=
  ⟨G.one_mul t (G.one t), negMor_over G⟩

/-- The kernel condition is an equality with the `2`-torsion, not only a
containment: the identity point lies in the Mumford kernel. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    (L : A.Modules) (h : KernelIsTwoTorsion G L) (R : Type u) [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    LocIsoOnBase (pullback.snd f t)
      ((Scheme.Modules.pullback (sliceAt (G.one t))).obj (mumfordBundle G L))
      (structureModule _) :=
  (h R t (G.one t)).2 (G.one_mul t (G.one t))

/-- The Mumford bundle is built from the dual `𝓗om(L, 𝒪_A)` of `L` itself,
not from a separately chosen sheaf. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    (L : A.Modules) :
    mumfordBundle G L =
      moduleTensor _ ((Scheme.Modules.pullback (addMor G)).obj L)
        (moduleTensor _
          ((Scheme.Modules.pullback (pullback.fst f f)).obj
            (MathlibExt.AlgebraicGeometry.BundleTrace.homSheaf A L
              (structureModule A)))
          ((Scheme.Modules.pullback (pullback.snd f f)).obj
            (MathlibExt.AlgebraicGeometry.BundleTrace.homSheaf A L
              (structureModule A)))) :=
  rfl

/-- Local isomorphism over the base is reflexive and symmetric on an
actual sheaf. -/
example {X Y : Scheme.{u}} (g : X ⟶ Y) (M M' : X.Modules)
    (h : LocIsoOnBase g M M') :
    LocIsoOnBase g M M ∧ LocIsoOnBase g M' M :=
  ⟨locIsoOnBase_refl g M, locIsoOnBase_symm h⟩

/-- Local isomorphism is local on the base, not on the total scheme: over
a field, whose spectrum is one point, it is an isomorphism over the whole
inverse image of the base. -/
example {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) (M M' : X.Modules)
    (h : LocIsoOnBase g M M') :
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).obj M ≅
      (Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).obj M') := by
  obtain ⟨U, hU, e⟩ := h default
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun y _ ↦ Subsingleton.elim default y ▸ hU
  exact e

/-- `RosatiCompatible` asks nothing of `star`: for the family of identity
maps both Rosati lifts are the identity of `A ×_S A`, so the condition holds
with the constant map on `Bool`, which is not an involution. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    (L : A.Modules) :
    RosatiCompatible G L (fun _ : Bool ↦ 𝟙 A) (fun _ ↦ Category.id_comp f)
      (fun _ ↦ true) := by
  intro b
  have h : rosatiLiftLeft (fun _ : Bool ↦ 𝟙 A) (fun _ ↦ Category.id_comp f) b =
      rosatiLiftRight (fun _ : Bool ↦ 𝟙 A) (fun _ ↦ Category.id_comp f)
        (fun _ ↦ true) b := by
    ext <;> simp [rosatiLiftLeft, rosatiLiftRight]
  rw [h]
  exact locIsoOnBase_refl _ _

end CanonicalPolarizationDataTest
