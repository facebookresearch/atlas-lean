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


public import Mathlib.Algebra.Homology.HomotopyCategory
public import MathlibExt.Algebra.Homology.HomotopyCofiberSplitting

/-!
# Mapping cylinders of complex morphisms

Let C be preadditive with binary biproducts, and c a complex shape with decidable relation. For
f:F→G, the mapping cylinder is Cyl(f)=Cof(a_f), where a_f=(id_F,-f):F→F⊕G. The endpoint
inclusions s:F→Cyl(f), t:G→Cyl(f) and projection π:Cyl(f)→G satisfy s≫π=f and t≫π=id_G.

A map from Cyl(f) to K is specified by maps e:F→K,g:G→K and a homotopy e∼f≫g, using the cofiber
descent with null homotopy of e-f≫g. Strict commutative squares induce cylinder maps.
Functoriality and the source-endpoint homotopy use the condition that every index has an
incoming differential relation.

Under that predecessor condition, π≫t is homotopic to the cylinder identity, so G and Cyl(f) are
homotopy equivalent. In the homotopy category the cylinder functor is naturally isomorphic to
target evaluation, with projection as its forward component.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Preadditive

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G K : HomologicalComplex C c}

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. The existence condition means that the homotopy cofiber of a_f is
available. It is the construction used to define Cyl(f). -/
abbrev HasMappingCylinder (f : F ⟶ G) : Prop :=
  HasHomotopyCofiber (biprod.lift (𝟙 F) (-f))

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. When that cofiber exists, Cyl(f)=Cof(id_F,-f) is a c-shaped complex. The
negative sign belongs to the G-coordinate of the defining map F→F⊕G. -/
noncomputable abbrev mappingCylinder (f : F ⟶ G)
    [HasMappingCylinder f] : HomologicalComplex C c :=
  homotopyCofiber (biprod.lift (𝟙 F) (-f))

namespace mappingCylinder

variable (f : F ⟶ G)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Let f:F→G be a morphism of c-shaped complexes and a_f=(id_F,-f):F→F⊕G. The map
a_f sends the F-coordinate by id_F into F⊕G and the G-coordinate by -f. Its two biproduct
components are id_F and -f. -/
noncomputable abbrev arrow : F ⟶ F ⊞ G :=
  biprod.lift (𝟙 F) (-f)

variable [HasMappingCylinder f]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). The source endpoint is s:F→Cyl(f), the first biproduct injection F→F⊕G followed by r. -/
noncomputable def source : F ⟶ mappingCylinder f :=
  biprod.inl ≫ homotopyCofiber.inr (arrow f)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). The target endpoint is t:G→Cyl(f), the second biproduct injection G→F⊕G followed by r. -/
noncomputable def target : G ⟶ mappingCylinder f :=
  biprod.inr ≫ homotopyCofiber.inr (arrow f)

omit [DecidableRel c.Rel] [HasMappingCylinder f] in
/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Let f:F→G be a morphism of c-shaped complexes and a_f=(id_F,-f):F→F⊕G. As maps
F→F⊕G, a_f=i_F-f≫i_G. This identity uses only biproduct maps and the additive complex morphisms. -/
theorem arrow_eq :
    arrow f = biprod.inl - f ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp [arrow]
  · simp [arrow]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). The equality a_f≫r=s-f≫t holds as a morphism F→Cyl(f), retaining the negative
f-coordinate of a_f. -/
theorem arrow_comp_inr :
    arrow f ≫ homotopyCofiber.inr (arrow f) =
      source f - f ≫ target f := by
  calc
    arrow f ≫ homotopyCofiber.inr (arrow f) =
        (biprod.inl - f ≫ biprod.inr) ≫
          homotopyCofiber.inr (arrow f) := by
      exact congrArg
        (fun k : F ⟶ F ⊞ G ↦
          k ≫ homotopyCofiber.inr (arrow f)) (arrow_eq f)
    _ = source f - f ≫ target f := by
      simp only [sub_comp, source, target, Category.assoc]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). Assume every j∈I admits i with c.Rel(i,j). There is a canonical homotopy s∼f≫t
obtained from the cofiber null homotopy of a_f≫r=s-f≫t. -/
noncomputable def sourceTargetHomotopy
    (H : ∀ j, ∃ i, c.Rel i j) :
    _root_.Homotopy (source f) (f ≫ target f) :=
  _root_.Homotopy.equivSubZero.symm
    ((_root_.Homotopy.ofEq (arrow_comp_inr f).symm).trans
      (homotopyCofiber.inrCompHomotopy (arrow f) H))

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Let f:F→G be a morphism of c-shaped complexes and a_f=(id_F,-f):F→F⊕G. The
composite a_f≫(f,id_G):F→G is zero, since its two contributions are f and -f. Its strict zero
equation gives the null homotopy used for the cylinder projection. -/
noncomputable def projectionHomotopy :
    _root_.Homotopy
      (arrow f ≫ biprod.desc f (𝟙 G)) 0 :=
  _root_.Homotopy.ofEq (by simp [arrow])

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). The projection π is cofiber descent of (f,id_G):F⊕G→G along its zero composite with
a_f. It is zero on shifted-source generators and has endpoint-coordinate map (f,id_G). -/
noncomputable def projection : mappingCylinder f ⟶ G :=
  homotopyCofiber.desc (arrow f) (biprod.desc f (𝟙 G))
    (projectionHomotopy f)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). The strict equation s≫π=f holds as a morphism F→G. -/
@[reassoc (attr := simp)]
theorem source_projection : source f ≫ projection f = f := by
  simp [source, projection]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). The equation t≫π=id_G holds. Thus the target endpoint is a section in the complex
category. -/
@[reassoc (attr := simp)]
theorem target_projection : target f ≫ projection f = 𝟙 G := by
  simp [target, projection]

section Desc

variable (e : F ⟶ K) (g : G ⟶ K)
  (h : _root_.Homotopy e (f ≫ g))

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Let f:F→G be a morphism of c-shaped complexes and a_f=(id_F,-f):F→F⊕G. For
e:F→K,g:G→K and a homotopy h:e∼f≫g, let h₀ be the induced null homotopy of a_f≫(e,g)=e-f≫g. The
homotopy h₀:a_f≫(e,g)∼0 follows from the equality a_f≫(e,g)=e-f≫g and the endpoint compatibility
homotopy h. -/
noncomputable def descHomotopy :
    _root_.Homotopy (arrow f ≫ biprod.desc e g) 0 :=
  (_root_.Homotopy.ofEq (by
      rw [arrow_eq, sub_comp, biprod.inl_desc,
        Category.assoc, biprod.inr_desc])).trans
    (_root_.Homotopy.equivSubZero h)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For e:F→K,g:G→K and a homotopy h:e∼f≫g, let h₀ be the induced null homotopy of
a_f≫(e,g)=e-f≫g. The map d:Cyl(f)→K is cofiber descent of (e,g) with h₀. It satisfies s≫d=e and
t≫d=g, and its shifted-source values are those of h₀. -/
noncomputable def desc : mappingCylinder f ⟶ K :=
  homotopyCofiber.desc (arrow f) (biprod.desc e g)
    (descHomotopy f e g h)

@[reassoc (attr := simp)]
theorem source_desc : source f ≫ desc f e g h = e := by
  simp [source, desc]

@[reassoc (attr := simp)]
theorem target_desc : target f ≫ desc f e g h = g := by
  simp [target, desc]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For e:F→K,g:G→K and a homotopy h:e∼f≫g, let h₀ be the induced null homotopy of
a_f≫(e,g)=e-f≫g. For i,j∈I with c.Rel(j,i), the inclusion ℓ_{i,j}:F_i→Cyl(f)_j satisfies
ℓ_{i,j}≫d_j=(h₀)_{i,j}, where d is the cylinder descent to K. -/
@[reassoc (attr := simp)]
theorem inlX_desc (i j : ι) (hji : c.Rel j i) :
    homotopyCofiber.inlX (arrow f) i j hji ≫
        (desc f e g h).f j =
      (descHomotopy f e g h).hom i j :=
  homotopyCofiber.inlX_desc_f (arrow f)
    (biprod.desc e g) (descHomotopy f e g h) i j hji

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For e:F→K,g:G→K and a homotopy h:e∼f≫g, let h₀ be the induced null homotopy of
a_f≫(e,g)=e-f≫g. For i∈I, the endpoint inclusion r_i:(F⊕G)_i→Cyl(f)_i satisfies r_i≫d_i=(e,g)_i.
This is the full endpoint-biproduct component of the descent. -/
@[reassoc (attr := simp)]
theorem inrX_desc (i : ι) :
    homotopyCofiber.inrX (arrow f) i ≫
        (desc f e g h).f i =
      (biprod.desc e g).f i :=
  homotopyCofiber.inrX_desc_f (arrow f)
    (biprod.desc e g) (descHomotopy f e g h) i

end Desc

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For i,j∈I with c.Rel(j,i), the shifted-source inclusion is ℓ_{i,j}:F_i→Cyl(f)_j. The
relation is reversed relative to the source differential, as required by the cofiber shift. -/
noncomputable abbrev inlX (i j : ι) (hij : c.Rel j i) :
    F.X i ⟶ (mappingCylinder f).X j :=
  homotopyCofiber.inlX (arrow f) i j hij

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For every i∈I, the endpoint inclusion r_i:(F⊕G)_i→Cyl(f)_i is the degree-i cofiber
target-coordinate inclusion. -/
noncomputable abbrev inrX (i : ι) :
    (F ⊞ G).X i ⟶ (mappingCylinder f).X i :=
  homotopyCofiber.inrX (arrow f) i

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
theorem inlX_projection (i j : ι) (hij : c.Rel j i) :
    inlX f i j hij ≫ (projection f).f j = 0 := by
  simp [projection, projectionHomotopy]

@[reassoc (attr := simp)]
theorem inrX_projection (i : ι) :
    inrX f i ≫ (projection f).f i =
      (biprod.desc f (𝟙 G)).f i :=
  homotopyCofiber.inrX_desc_f _ _ _ _

section Functoriality

variable {F' G' : HomologicalComplex C c} {f' : F' ⟶ G'}
  [HasMappingCylinder f']

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Let f:F→G be a morphism of c-shaped complexes and a_f=(id_F,-f):F→F⊕G. For a
strict square from f:F→G to f':F'→G' with maps a_L:F→F',a_R:G→G' and f≫a_R=a_L≫f', the induced
square a_f→a_{f'} has source map a_L and target map a_L⊕a_R. -/
noncomputable def arrowMap
    (f' : F' ⟶ G')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    Arrow.mk (arrow f) ⟶ Arrow.mk (arrow f') where
  left := a.left
  right := biprod.map a.left a.right
  w := by
    apply biprod.hom_ext
    · simp [arrow]
    · simp [arrow]

omit [DecidableRel c.Rel] [HasMappingCylinder f]
    [HasMappingCylinder f'] in
@[simp]
theorem arrowMap_left
    (f' : F' ⟶ G')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    (arrowMap f f' a).left = a.left :=
  rfl

omit [DecidableRel c.Rel] [HasMappingCylinder f]
    [HasMappingCylinder f'] in
@[simp]
theorem arrowMap_right
    (f' : F' ⟶ G')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    (arrowMap f f' a).right = biprod.map a.left a.right :=
  rfl

omit [DecidableRel c.Rel] [HasMappingCylinder f] in
@[simp]
theorem arrowMap_id :
    arrowMap f f (𝟙 (Arrow.mk f)) =
      𝟙 (Arrow.mk (arrow f)) := by
  apply Arrow.hom_ext
  · rfl
  · apply biprod.hom_ext <;> simp

omit [DecidableRel c.Rel] [HasMappingCylinder f]
    [HasMappingCylinder f'] in
@[reassoc]
theorem arrowMap_comp
    (f' : F' ⟶ G')
    {F'' G'' : HomologicalComplex C c} (f'' : F'' ⟶ G'')
    (a : Arrow.mk f ⟶ Arrow.mk f')
    (b : Arrow.mk f' ⟶ Arrow.mk f'') :
    arrowMap f f'' (a ≫ b) =
      arrowMap f f' a ≫ arrowMap f' f'' b := by
  apply Arrow.hom_ext
  · rfl
  · apply biprod.hom_ext <;> simp [Category.assoc]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). Let f':F'→G' have a cylinder, and a=(a_L,a_R) be a strict square with f≫a_R=a_L≫f'.
Assume every j∈I admits i with c.Rel(i,j). The induced map Cyl(a):Cyl(f)→Cyl(f') is the cofiber
map of the square a_f→a_{f'}. It maps endpoint coordinates by a_L⊕a_R and shifted source
coordinates by a_L. -/
noncomputable def map (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    mappingCylinder f ⟶ mappingCylinder f' :=
  homotopyCofiber.mapArrowHom (arrow f) (arrow f') H
    (arrowMap f f' a)

@[simp]
theorem map_id (H : ∀ j, ∃ i, c.Rel i j) :
    map f f H (𝟙 (Arrow.mk f)) =
      𝟙 (mappingCylinder f) := by
  change homotopyCofiber.mapArrowHom (arrow f) (arrow f) H
      (arrowMap f f (𝟙 (Arrow.mk f))) = 𝟙 _
  rw [arrowMap_id]
  exact homotopyCofiber.mapArrowHom_id (arrow f) H

@[reassoc]
theorem map_comp (H : ∀ j, ∃ i, c.Rel i j)
    {F'' G'' : HomologicalComplex C c} {f'' : F'' ⟶ G''}
    [HasMappingCylinder f'']
    (a : Arrow.mk f ⟶ Arrow.mk f')
    (b : Arrow.mk f' ⟶ Arrow.mk f'') :
    map f f'' H (a ≫ b) = map f f' H a ≫ map f' f'' H b := by
  change homotopyCofiber.mapArrowHom (arrow f) (arrow f'') H
      (arrowMap f f'' (a ≫ b)) = _
  rw [arrowMap_comp f f' f'' a b]
  exact homotopyCofiber.mapArrowHom_comp
    (arrow f) (arrow f') (arrow f'') H
      (arrowMap f f' a) (arrowMap f' f'' b)

@[reassoc (attr := simp)]
theorem source_map (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    source f ≫ map f f' H a = a.left ≫ source f' := by
  simp [source, map, Category.assoc,
    homotopyCofiber.inr_mapArrowHom]

@[reassoc (attr := simp)]
theorem target_map (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    target f ≫ map f f' H a = a.right ≫ target f' := by
  simp [target, map, Category.assoc,
    homotopyCofiber.inr_mapArrowHom]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). Let f':F'→G' have a cylinder, and a=(a_L,a_R) be a strict square with f≫a_R=a_L≫f'.
Assume every j∈I admits i with c.Rel(i,j). The projection square is Cyl(a)≫π_{f'}=π_f≫a_R as
maps Cyl(f)→G'. -/
@[reassoc]
theorem map_projection (f' : F' ⟶ G')
    (H : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    map f f' H a ≫ projection f' =
      projection f ≫ a.right := by
  apply homotopyCofiber.mapArrowHom_desc_naturality H
      (arrowMap f f' a)
      (biprod.desc f (𝟙 G))
      (biprod.desc f' (𝟙 G'))
      (projectionHomotopy f) (projectionHomotopy f') a.right
  · apply biprod.hom_ext'
    · simp
    · simp
  · intro i j
    simp [projectionHomotopy]

end Functoriality

variable (C c)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. The arrow functor sends f:F→G to a_f=(id_F,-f):F→F⊕G. A strict square (a_L,a_R)
is sent to the square (a_L,a_L⊕a_R). These assignments preserve identities and composition. -/
noncomputable def arrowFunctor :
    Arrow (HomologicalComplex C c) ⥤
      Arrow (HomologicalComplex C c) where
  obj f := Arrow.mk (arrow f.hom)
  map {f f'} a := arrowMap f.hom f'.hom a
  map_id f := arrowMap_id f.hom
  map_comp {f f' f''} a b :=
    arrowMap_comp f.hom f'.hom f''.hom a b

variable {C c}

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). The
functor Arrow(HomologicalComplex(C,c))→HomologicalComplex(C,c) sends f to Cyl(f)=Cof(id_F,-f)
and a strict square to its cofiber-induced cylinder map. -/
noncomputable def functor (H : ∀ j, ∃ i, c.Rel i j) :
    Arrow (HomologicalComplex C c) ⥤ HomologicalComplex C c :=
  arrowFunctor C c ⋙ HomologicalComplex.homotopyCofiberFunctor H

@[simp]
theorem functor_obj (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (functor H).obj f = mappingCylinder f.hom :=
  rfl

@[simp]
theorem functor_map (H : ∀ j, ∃ i, c.Rel i j)
    {f f' : Arrow (HomologicalComplex C c)} (a : f ⟶ f') :
    (functor H).map a = map f.hom f'.hom H a :=
  rfl

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). The
endpoints s_f:F→Cyl(f) define a natural transformation from source evaluation to the cylinder
functor. For a strict square a:f→f', a_L≫s_{f'}=s_f≫Cyl(a). -/
noncomputable def sourceNatTrans (H : ∀ j, ∃ i, c.Rel i j) :
    (Arrow.leftFunc : Arrow (HomologicalComplex C c) ⥤ _) ⟶
      functor H where
  app f := source f.hom
  naturality {f f'} a := (source_map f.hom f'.hom H a).symm

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). The maps
t_f:G→Cyl(f) define a natural transformation from target evaluation to the cylinder functor. Its
square is a_R≫t_{f'}=t_f≫Cyl(a). -/
noncomputable def targetNatTrans (H : ∀ j, ∃ i, c.Rel i j) :
    (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) ⟶
      functor H where
  app f := target f.hom
  naturality {f f'} a := (target_map f.hom f'.hom H a).symm

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). The maps
π_f:Cyl(f)→G define a natural transformation from the cylinder functor to target evaluation. For
a strict square a, Cyl(a)≫π_{f'}=π_f≫a_R. -/
noncomputable def projectionNatTrans
    (H : ∀ j, ∃ i, c.Rel i j) :
    functor H ⟶
      (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) where
  app f := projection f.hom
  naturality {f f'} a := map_projection f.hom f'.hom H a

@[simp]
theorem targetNatTrans_comp_projectionNatTrans
    (H : ∀ j, ∃ i, c.Rel i j) :
    targetNatTrans H ≫ projectionNatTrans H =
      𝟙 (Arrow.rightFunc :
        Arrow (HomologicalComplex C c) ⥤ _) := by
  ext f
  simp [targetNatTrans, projectionNatTrans]

/-!
## The signed deformation retraction

Let q_i:Cyl(f)_i→(F⊕G)_i be the endpoint-coordinate projection and ℓ_{i,j}:F_i→Cyl(f)_j the
shifted-source inclusion for c.Rel(j,i). The degreewise homotopy map is
h_{i,j}=q_i≫pr_F,i≫ℓ_{i,j}. Its boundary defines a null-homotopic endomorphism N.

When every index has a predecessor, the generator formulas identify N=id_Cyl-π≫t. Negating the
resulting null homotopy gives the deformation homotopy π≫t∼id_Cyl. Together with the strict
equation t≫π=id_G, these maps form the homotopy equivalence.
-/

section Retraction

variable (H : ∀ j, ∃ i, c.Rel i j)

namespace projectionCompTargetHomotopy

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For c.Rel(j,i), put h_{i,j}=q_i≫pr_F,i≫ℓ_{i,j}, where q_i projects to the endpoint
biproduct. The boundary of these homotopy maps defines N:Cyl(f)→Cyl(f), canonically
null-homotopic. If every j admits i with c.Rel(i,j), then N=id_Cyl-π≫t. -/
noncomputable def nullHomotopicMap :
    mappingCylinder f ⟶ mappingCylinder f :=
  _root_.Homotopy.nullHomotopicMap'
    (fun i j hij ↦
      homotopyCofiber.sndX (arrow f) i ≫
        (biprod.fst : F ⊞ G ⟶ F).f i ≫
          inlX f i j hij)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). For the degreewise maps h_{i,j}=q_i≫pr_F,i≫ℓ_{i,j}, the associated boundary
endomorphism N has a homotopy N∼0 with these components. Here q_i is endpoint-coordinate
projection and c.Rel(j,i). -/
noncomputable def nullHomotopy :
    _root_.Homotopy (nullHomotopicMap f) 0 :=
  _root_.Homotopy.nullHomotopy' _

theorem inlX_nullHomotopicMap_f
    (i j : ι) (hij : c.Rel j i) :
    inlX f i j hij ≫ (nullHomotopicMap f).f j =
      inlX f i j hij ≫
        (𝟙 _ - projection f ≫ target f).f j := by
  dsimp [nullHomotopicMap]
  by_cases! hj : ∃ k, c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [Category.assoc,
      _root_.Homotopy.nullHomotopicMap'_f hjk hij,
      homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij,
      Preadditive.add_comp, Preadditive.comp_add,
      homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,
      zero_comp, add_zero, comp_sub, inlX_projection_assoc,
      Category.comp_id, sub_zero, ← HomologicalComplex.comp_f_assoc,
      biprod.lift_fst, id_f, Category.id_comp]
  · simp only [_root_.Homotopy.nullHomotopicMap'_f_of_not_rel_right
        hij hj,
      homotopyCofiber_d, Category.assoc, comp_sub, Category.comp_id,
      homotopyCofiber.d_sndX_assoc _ _ _ hij,
      Preadditive.add_comp, Preadditive.comp_add,
      zero_comp, add_zero, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc,
      ← HomologicalComplex.comp_f_assoc, biprod.lift_fst,
      id_f, Category.id_comp, inlX_projection_assoc, sub_zero]

include H in
theorem inrX_nullHomotopicMap_f (j : ι) :
    inrX f j ≫ (nullHomotopicMap f).f j =
      inrX f j ≫
        (𝟙 _ - projection f ≫ target f).f j := by
  obtain ⟨i, hij⟩ := H j
  dsimp [nullHomotopicMap]
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Category.assoc,
      _root_.Homotopy.nullHomotopicMap'_f hij hjk,
      homotopyCofiber_d, Preadditive.comp_add,
      homotopyCofiber.inrX_d_assoc,
      homotopyCofiber.inrX_sndX_assoc, comp_sub,
      inrX_projection_assoc, Category.comp_id,
      ← HomologicalComplex.comp_f_assoc,
      homotopyCofiber.inlX_d _ _ _ _ _ hjk]
    rw [← cancel_epi (biprodXIso F G j).inv]
    ext
    · simp [target, arrow_eq]
    · simp [target, arrow_eq]
  · simp only [not_exists] at hj
    simp only [Category.assoc,
      _root_.Homotopy.nullHomotopicMap'_f_of_not_rel_left hij hj,
      homotopyCofiber_d,
      homotopyCofiber.inlX_d' _ _ _ _ (hj _),
      homotopyCofiber.inrX_sndX_assoc,
      comp_sub, inrX_projection_assoc, Category.comp_id,
      target, HomologicalComplex.comp_f,
      homotopyCofiber.inr_f]
    rw [← cancel_epi (biprodXIso F G j).inv]
    ext
    · simp [arrow_eq]
    · simp [arrow_eq]

include H in
theorem nullHomotopicMap_eq :
    nullHomotopicMap f =
      𝟙 _ - projection f ≫ target f := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (arrow f)
      (c.next i) i hi
      (inlX_nullHomotopicMap_f f _ _ hi)
      (inrX_nullHomotopicMap_f f H _)
  · exact homotopyCofiber.ext_from_X' (arrow f) i hi
      (inrX_nullHomotopicMap_f f H _)

end projectionCompTargetHomotopy

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). Assume every j∈I admits i with c.Rel(i,j). The deformation homotopy is π≫t∼id_Cyl. It
is obtained by identifying the null-homotopic endomorphism N with id_Cyl-π≫t and negating that
null homotopy. -/
noncomputable def projectionCompTargetHomotopy :
    _root_.Homotopy (projection f ≫ target f)
      (𝟙 (mappingCylinder f)) :=
  (_root_.Homotopy.equivSubZero.symm
    ((_root_.Homotopy.ofEq
      (projectionCompTargetHomotopy.nullHomotopicMap_eq f H).symm).trans
        (projectionCompTargetHomotopy.nullHomotopy f))).symm

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Let f:F→G be a morphism of c-shaped complexes and
a_f=(id_F,-f):F→F⊕G. Assume Cyl(f)=Cof(a_f) exists. Write r:F⊕G→Cyl(f) for the cofiber
inclusion, s=i_F≫r and t=i_G≫r for its endpoints, and π:Cyl(f)→G for the projection induced by
(f,id_G). Assume every j∈I admits i with c.Rel(i,j). The homotopy equivalence G≃Cyl(f) has
forward map t and inverse π. Its first composite is t≫π=id_G, and its second has the deformation
homotopy π≫t∼id_Cyl. -/
@[simps]
noncomputable def homotopyEquiv :
    _root_.HomotopyEquiv G (mappingCylinder f) where
  hom := target f
  inv := projection f
  homotopyHomInvId := _root_.Homotopy.ofEq (by simp)
  homotopyInvHomId := projectionCompTargetHomotopy f H

end Retraction

section HomotopyCategory

variable (C c)

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). For the
quotient Q:HomologicalComplex(C,c)→HomotopyCategory(C,c), there is a natural isomorphism
Q∘Cyl≅Q∘targetEval on the arrow category. At f its forward map is Q(π_f) and inverse is Q(t_f). -/
noncomputable def homotopyCategoryNatIso
    (H : ∀ j, ∃ i, c.Rel i j) :
    functor H ⋙ HomotopyCategory.quotient C c ≅
      (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) ⋙
        HomotopyCategory.quotient C c :=
  NatIso.ofComponents
    (fun f ↦ (HomotopyCategory.isoOfHomotopyEquiv
      (homotopyEquiv f.hom H)).symm)
    (fun {f f'} a ↦ by
      change (HomotopyCategory.quotient C c).map
            (map f.hom f'.hom H a) ≫
          (HomotopyCategory.quotient C c).map (projection f'.hom) =
        (HomotopyCategory.quotient C c).map (projection f.hom) ≫
          (HomotopyCategory.quotient C c).map a.right
      rw [← Functor.map_comp, ← Functor.map_comp,
        map_projection f.hom f'.hom H a])

variable {C c}

@[simp]
theorem homotopyCategoryNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (homotopyCategoryNatIso C c H).hom.app f =
      (HomotopyCategory.quotient C c).map (projection f.hom) :=
  rfl

@[simp]
theorem homotopyCategoryNatIso_inv_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (homotopyCategoryNatIso C c H).inv.app f =
      (HomotopyCategory.quotient C c).map (target f.hom) :=
  rfl

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). Let Q be
the homotopy-category quotient functor. For f:F→G and comparison Γ_f:Q(Cyl(f))≅Q(G), one has
Q(t_f)≫Γ_f.hom=id_{Q(G)}. The comparison's forward component is Q(π_f). -/
@[reassoc]
theorem quotient_target_comp_homotopyCategoryNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (HomotopyCategory.quotient C c).map (target f.hom) ≫
        (homotopyCategoryNatIso C c H).hom.app f =
      𝟙 ((HomotopyCategory.quotient C c).obj f.right) := by
  rw [homotopyCategoryNatIso_hom_app,
    ← CategoryTheory.Functor.map_comp, target_projection,
    CategoryTheory.Functor.map_id]

/-- Let C be preadditive with binary biproducts in object/morphism universes u,v, and c a complex
shape on I in w. Assume c.Rel is decidable. Assume every j∈I admits i with c.Rel(i,j). Let Q be
the homotopy-category quotient functor. For f:F→G and Γ_f:Q(Cyl(f))≅Q(G), Q(s_f)≫Γ_f.hom=Q(f).
Thus the source endpoint projects to the given arrow in the homotopy category. -/
@[reassoc]
theorem quotient_source_comp_homotopyCategoryNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : Arrow (HomologicalComplex C c)) :
    (HomotopyCategory.quotient C c).map (source f.hom) ≫
        (homotopyCategoryNatIso C c H).hom.app f =
      (HomotopyCategory.quotient C c).map f.hom := by
  rw [homotopyCategoryNatIso_hom_app,
    ← CategoryTheory.Functor.map_comp,
    source_projection]

end HomotopyCategory

end mappingCylinder

end HomologicalComplex

end
