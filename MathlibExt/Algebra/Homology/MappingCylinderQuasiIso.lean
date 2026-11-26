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


public import Mathlib.Algebra.Homology.QuasiIso
public import MathlibExt.Algebra.Homology.MappingCylinder

/-!
# Quasi-isomorphisms from a mapping-cylinder deformation retraction

Let C be preadditive with binary biproducts and c a complex shape with decidable relation. For
f:F→G, its mapping cylinder is the homotopy cofiber of (id_F,-f):F→F⊕G.

Assume the cylinder exists and every index j admits i with c.Rel(i,j). The target endpoint
t:G→Cyl(f) and projection π:Cyl(f)→G form a homotopy equivalence. If G and Cyl(f) have homology
at every index, both maps are quasi-isomorphisms and induce inverse homology isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.mappingCylinder

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G : HomologicalComplex C c}

/-- Let C be preadditive with binary biproducts, in object/morphism universes u,v, and c a complex
shape on I in w with decidable relation. Let f:F→G be a morphism of c-shaped complexes whose
cylinder Cyl(f)=Cof(id_F,-f) exists. Assume every j∈I has an incoming relation c.Rel(i,j), and
G,Cyl(f) have homology at every index. The endpoint t:G→Cyl(f) is a quasi-isomorphism: each
H_i(t):H_iG→H_iCyl(f) is an isomorphism. It is the forward map of the cylinder homotopy
equivalence. -/
theorem target_quasiIso (f : F ⟶ G) [HasMappingCylinder f]
    (H : ∀ j, ∃ i, c.Rel i j)
    [∀ i, G.HasHomology i]
    [∀ i, (HomologicalComplex.mappingCylinder f).HasHomology i] :
    QuasiIso (target f) :=
  (homotopyEquiv f H).quasiIso_hom

/-- Let C be preadditive with binary biproducts, in object/morphism universes u,v, and c a complex
shape on I in w with decidable relation. Let f:F→G be a morphism of c-shaped complexes whose
cylinder Cyl(f)=Cof(id_F,-f) exists. Assume every j admits an incoming relation and homology
exists in all degrees of G,Cyl(f). The projection π:Cyl(f)→G is a quasi-isomorphism. Its
homology maps are inverse to those of the target endpoint, through their deformation-retraction
homotopy equivalence. -/
theorem projection_quasiIso (f : F ⟶ G) [HasMappingCylinder f]
    (H : ∀ j, ∃ i, c.Rel i j)
    [∀ i, G.HasHomology i]
    [∀ i, (HomologicalComplex.mappingCylinder f).HasHomology i] :
    QuasiIso (projection f) :=
  (homotopyEquiv f H).quasiIso_inv

end HomologicalComplex.mappingCylinder

end
