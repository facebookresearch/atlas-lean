/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Group and coefficient functoriality in degree-three cohomology

Let k be a commutative ring, f:G→H a group homomorphism in universe u, A an H-representation,
and φ:Res_f A→B an equivariant k-linear map to a G-representation. In degree n, the cochain map
sends z to (g₁,…,g_n)↦φ(z(f(g₁),…,f(g_n))).

The degree-two, degree-three, and degree-four maps form a morphism of the short complexes
computing third cohomology. Their cycle map restricts this formula to Z³(H,A)→Z³(G,B). The
resulting cohomology map satisfies map_{f,φ}([z])=[mapCocycles_{f,φ}(z)] in H³(G,B).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Representation

universe u

namespace groupCohomology

open ShortComplex

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A : Rep k H} {B : Rep k G}
variable (f : G →* H) (φ : Rep.res f A ⟶ B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem isoCocycles₃_hom_comp_i (A : Rep k G) :
    (isoCocycles₃ A).hom ≫
        (shortComplexH3 A).moduleCatLeftHomologyData.i =
      iCocycles A 3 ≫ (cochainsIso₃ A).hom := by
  simp [isoCocycles₃, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem isoCocycles₃_inv_comp_iCocycles (A : Rep k G) :
    (isoCocycles₃ A).inv ≫ iCocycles A 3 =
      (shortComplexH3 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₃ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₃_hom_comp_i A⟩).w

/-- Let k be a commutative ring, G,H groups in the given universe u, A a k-linear H-representation,
and B a k-linear G-representation. Let f:G→H be a homomorphism and φ:Res_f A→B an equivariant
k-linear coefficient map. The k-linear cochain map C⁴(H,A)→C⁴(G,B) sends z to
z'(g,h,i,j)=φ(z(f(g),f(h),f(i),f(j))). The four group arguments are transformed in order and the
coefficient map is applied afterwards. -/
noncomputable abbrev cochainsMap₄ :
    ModuleCat.of k (H × H × H × H → A) ⟶
      ModuleCat.of k (G × G × G × G → B) :=
  ModuleCat.ofHom <| φ.hom.toLinearMap.compLeft (G × G × G × G) ∘ₗ
    LinearMap.funLeft k A
      (Prod.map f (Prod.map f (Prod.map f f)))

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cochainsMap_f_4_comp_cochainsIso₄ :
    (cochainsMap f φ).f 4 ≫ (cochainsIso₄ B).hom =
      (cochainsIso₄ A).hom ≫ cochainsMap₄ f φ := by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G,H groups in the given universe u, A a k-linear H-representation,
and B a k-linear G-representation. Let f:G→H be a homomorphism and φ:Res_f A→B an equivariant
k-linear coefficient map. The maps in degrees 2,3,4 form a morphism
(C²(H,A)→C³(H,A)→C⁴(H,A))→(C²(G,B)→C³(G,B)→C⁴(G,B)). The degree-n component sends z to φ∘z∘f^n,
and these components commute with δ₂ and δ₃ by equivariance of φ. -/
@[simps]
noncomputable def mapShortComplexH3 :
    shortComplexH3 A ⟶ shortComplexH3 B where
  τ₁ := cochainsMap₂ f φ
  τ₂ := cochainsMap₃ f φ
  τ₃ := cochainsMap₄ f φ
  comm₁₂ := by
    ext x
    funext g
    simp [shortComplexH3, ← Rep.hom_comm_apply φ]
  comm₂₃ := by
    ext x
    funext g
    simp [shortComplexH3, d₃₄, ← Rep.hom_comm_apply φ]

/-- Let k be a commutative ring, G,H groups in the given universe u, A a k-linear H-representation,
and B a k-linear G-representation. Let f:G→H be a homomorphism and φ:Res_f A→B an equivariant
k-linear coefficient map. The k-linear map Z³(H,A)→Z³(G,B) sends a cocycle z to
z'(g,h,i)=φ(z(f(g),f(h),f(i))). It is the cycle map induced by the morphism of explicit
degree-three short complexes. -/
noncomputable abbrev mapCocycles₃ :
    ModuleCat.of k (cocycles₃ A) ⟶ ModuleCat.of k (cocycles₃ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH3 f φ)
    (shortComplexH3 A).moduleCatLeftHomologyData
    (shortComplexH3 B).moduleCatLeftHomologyData

@[simp]
theorem coe_mapCocycles₃ (x) :
    ⇑(mapCocycles₃ f φ x) = cochainsMap₃ f φ x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cocyclesMap_comp_isoCocycles₃_hom :
    cocyclesMap f φ 3 ≫ (isoCocycles₃ B).hom =
      (isoCocycles₃ A).hom ≫ mapCocycles₃ f φ := by
  simp [← cancel_mono
      (shortComplexH3 B).moduleCatLeftHomologyData.i,
    mapShortComplexH3, cochainsMap_f_3_comp_cochainsIso₃ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H3π_comp_map :
    H3π A ≫ map f φ 3 = mapCocycles₃ f φ ≫ H3π B := by
  simp [H3π, Iso.inv_comp_eq,
    ← cocyclesMap_comp_isoCocycles₃_hom_assoc]

end groupCohomology
