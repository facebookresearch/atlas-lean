/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Basic
public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeComparison
public import MathlibExt.CategoryTheory.Abelian.Projective.ResolutionComparison

/-!
# Comparisons of Cartan–Eilenberg resolutions

Let C be abelian, g : L → L′ a map of nonnegative complexes, and P,Q chosen Cartan–Eilenberg
resolutions. A comparison over g consists of boundary and homology projective-resolution lifts
and compatible strict comparisons of the cycle and term horseshoes. In original degree j, the
cycle horseshoe uses the boundary endpoint j+1; the term horseshoe uses boundary endpoint j and
reuses that same cycle comparison.

Comparisons exist but involve choices. Each comparison induces strict maps of term complexes and
resolution-degree-first bicomplexes. Identity and composition of chosen comparison data induce
the corresponding strict maps. The four underlying families determine a comparison, and the
identity, composition and equality-transport operations satisfy their unit and associativity
laws.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L L' : ChainComplex C ℕ}
variable (P : CartanEilenbergResolution L) (Q : CartanEilenbergResolution L')
variable (g : L ⟶ L')

namespace CartanEilenbergResolution

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. A comparison specifies projective-resolution lifts of
the outgoing-boundary maps and homology maps, and strict comparisons of the two horseshoe rows.
At original degree j, the cycle comparison has boundary endpoint in degree j+1 and homology
endpoint in degree j; the term comparison uses that same cycle comparison and boundary endpoint
j. -/
structure Hom where
  /-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. The degree-j boundary
component is a projective-resolution morphism from P's resolution of Bⱼ⁽out⁾(L) to Q's
resolution of Bⱼ⁽out⁾(L′), covering the outgoing-image map induced by g. -/
  boundaryHom (j : ℕ) :
    ProjectiveResolution.Hom (P.boundaryResolution j)
      (Q.boundaryResolution j) (boundaryFromMap g j)
  /-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. The degree-j homology
component is a morphism of the chosen projective resolutions of Hⱼ(L) and Hⱼ(L′), covering
Hⱼ(g). -/
  homologyHom (j : ℕ) :
    ProjectiveResolution.Hom (P.homologyResolution j)
      (Q.homologyResolution j) (homologyMap g j)
  /-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. The degree-j cycle component
is a strict comparison of the boundary–cycle–homology horseshoes, with endpoints the boundary
lift in degree j+1 and the homology lift in degree j. -/
  cyclesHom (j : ℕ) :
    ProjectiveResolution.HorseshoeData.Hom
      (H := P.cyclesHorseshoe j) (H' := Q.cyclesHorseshoe j)
      (φ := boundaryCyclesHomologyMap g j)
      (u := boundaryHom (j + 1)) (w := homologyHom j)
  /-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. The degree-j term component is
a strict comparison of the cycles–term–boundary horseshoes. Its left endpoint is F's degree-j
cycle comparison and its right endpoint is F's degree-j boundary lift. -/
  termHom (j : ℕ) :
    ProjectiveResolution.HorseshoeData.Hom
      (H := P.termHorseshoe j) (H' := Q.termHorseshoe j)
      (φ := cyclesTermBoundaryMap g j)
      (u := (cyclesHom j).toProjectiveResolutionHom)
      (w := boundaryHom j)

namespace Hom

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Two comparisons F,G over g are equal if their boundary,
homology, cycle and term chain maps agree in every original degree. Thus the four underlying
families determine the complete comparison. -/
@[ext]
theorem ext {F G : Hom P Q g}
    (hb : ∀ j : ℕ, (F.boundaryHom j).hom = (G.boundaryHom j).hom)
    (hh : ∀ j : ℕ, (F.homologyHom j).hom = (G.homologyHom j).hom)
    (hc : ∀ j : ℕ, (F.cyclesHom j).hom = (G.cyclesHom j).hom)
    (ht : ∀ j : ℕ, (F.termHom j).hom = (G.termHom j).hom) : F = G := by
  obtain ⟨bF, hF, cF, tF⟩ := F
  obtain ⟨bG, hG, cG, tG⟩ := G
  have hb' : bF = bG :=
    funext fun j => ProjectiveResolution.Hom.ext (hb j)
  have hh' : hF = hG :=
    funext fun j => ProjectiveResolution.Hom.ext (hh j)
  subst hb'
  subst hh'
  have hc' : cF = cG :=
    funext fun j =>
      ProjectiveResolution.HorseshoeData.Hom.ext (h := hc j)
  subst hc'
  have ht' : tF = tG :=
    funext fun j =>
      ProjectiveResolution.HorseshoeData.Hom.ext (h := ht j)
  subst ht'
  rfl

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. In the chosen cycle horseshoe
coordinates PBⱼ₊₁,ₐ ⊕ PHⱼ,ₐ, the comparison has the prescribed boundary and homology diagonal
maps. The boundary-to-target-homology component is zero, and the homology-to-target-boundary
cross component is the remaining possible component. -/
theorem cyclesHom_spec (F : Hom P Q g) (j : ℕ) :
    (F.cyclesHom j).Spec
      (sH := P.cyclesSpec j) (sH' := Q.cyclesSpec j) :=
  (F.cyclesHom j).spec
    (sH := P.cyclesSpec j) (sH' := Q.cyclesSpec j)

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. In the chosen term coordinates
PCⱼ,ₐ ⊕ PBⱼ,ₐ, the comparison has the prescribed cycle and boundary diagonal maps. The
cycles-to-target-boundary component vanishes; the boundary-to-target-cycles cross component is
free. -/
theorem termHom_spec (F : Hom P Q g) (j : ℕ) :
    (F.termHom j).Spec (sH := P.termSpec j) (sH' := Q.termSpec j) :=
  (F.termHom j).spec (sH := P.termSpec j) (sH' := Q.termSpec j)

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For every j ∈ ℕ, the term
comparison maps commute with the lifted original differential Dⱼ: Q.Dⱼ ∘ F.termⱼ₊₁ = F.termⱼ ∘
P.Dⱼ. No sign occurs in this square. -/
@[reassoc]
theorem termDifferential_naturality (F : Hom P Q g) (j : ℕ) :
    (F.termHom (j + 1)).hom ≫ Q.termDifferential j =
      P.termDifferential j ≫ (F.termHom j).hom := by
  have hterm : (P.termHorseshoe j).i ≫ (F.termHom j).hom =
      (F.cyclesHom j).hom ≫ (Q.termHorseshoe j).i :=
    (F.termHom j).comm_i
  rw [P.termDifferential_eq j, Q.termDifferential_eq j]
  simp only [Category.assoc]
  rw [reassoc_of% (F.termHom (j + 1)).comm_p]
  rw [← reassoc_of% (F.cyclesHom j).comm_i]
  rw [← hterm]

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. The degree-j term-resolution
chain maps assemble into a chain map P.termComplex → Q.termComplex in original degree, covering
the original map g. -/
noncomputable def termComplexHom (F : Hom P Q g) :
    P.termComplex ⟶ Q.termComplex :=
  ChainComplex.ofHom (fun j => (F.termHom j).hom) (fun j => by
    rw [P.termComplex_d j, Q.termComplex_d j]
    exact termDifferential_naturality P Q g F j)

@[simp]
theorem termComplexHom_f (F : Hom P Q g) (j : ℕ) :
    F.termComplexHom.f j = (F.termHom j).hom :=
  rfl

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. Flipping the term-complex map
gives a strict map P.bicomplex → Q.bicomplex. In entry (a,j), it is the resolution-degree-a
component of the degree-j term comparison. -/
noncomputable def bicomplexHom (F : Hom P Q g) :
    P.bicomplex ⟶ Q.bicomplex :=
  (HomologicalComplex₂.flipFunctor C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)).map F.termComplexHom

@[simp]
theorem bicomplexHom_f_f (F : Hom P Q g) (a j : ℕ) :
    (F.bicomplexHom.f a).f j = (F.termHom j).hom.f a :=
  rfl

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution of L. The chosen
identity comparison P → P over id_L has identity boundary and homology lifts and identity cycle
and term horseshoe comparisons. -/
def id (P : CartanEilenbergResolution L) : Hom P P (𝟙 L) where
  boundaryHom j := (ProjectiveResolution.Hom.id
    (P.boundaryResolution j)).cast (boundaryFromMap_id L j).symm
  homologyHom j := (ProjectiveResolution.Hom.id
    (P.homologyResolution j)).cast (homologyMap_id L j).symm
  cyclesHom j :=
    (ProjectiveResolution.HorseshoeData.Hom.id (P.cyclesHorseshoe j)).cast
      (boundaryCyclesHomologyMap_id L j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)
  termHom j :=
    (ProjectiveResolution.HorseshoeData.Hom.id (P.termHorseshoe j)).cast
      (cyclesTermBoundaryMap_id L j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)

@[simp]
theorem id_boundaryHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).boundaryHom j).hom =
      𝟙 (P.boundaryResolution j).complex :=
  rfl

@[simp]
theorem id_homologyHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).homologyHom j).hom =
      𝟙 (P.homologyResolution j).complex :=
  rfl

@[simp]
theorem id_cyclesHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).cyclesHom j).hom =
      𝟙 (P.cyclesResolution j).complex :=
  rfl

@[simp]
theorem id_termHom_hom (P : CartanEilenbergResolution L) (j : ℕ) :
    ((Hom.id P).termHom j).hom = 𝟙 (P.termResolution j).complex :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For a third resolution R of L″
and a comparison G : Q → R over h : L′ → L″, the composite comparison P → R covers h ∘ g. Each
of its four underlying chain-map families is the composite of the corresponding families of F
and G. -/
def comp {L'' : ChainComplex C ℕ} {R : CartanEilenbergResolution L''}
    {h : L' ⟶ L''} (F : Hom P Q g) (G : Hom Q R h) : Hom P R (g ≫ h) where
  boundaryHom j := ((F.boundaryHom j).comp (G.boundaryHom j)).cast
    (boundaryFromMap_comp g h j).symm
  homologyHom j := ((F.homologyHom j).comp (G.homologyHom j)).cast
    (homologyMap_comp g h j).symm
  cyclesHom j :=
    ((F.cyclesHom j).comp (G.cyclesHom j)).cast
      (boundaryCyclesHomologyMap_comp g h j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)
  termHom j :=
    ((F.termHom j).comp (G.termHom j)).cast
      (cyclesTermBoundaryMap_comp g h j).symm
      (ProjectiveResolution.Hom.ext rfl) (ProjectiveResolution.Hom.ext rfl)

@[simp]
theorem comp_boundaryHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).boundaryHom j).hom =
      (F.boundaryHom j).hom ≫ (G.boundaryHom j).hom :=
  rfl

@[simp]
theorem comp_homologyHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).homologyHom j).hom =
      (F.homologyHom j).hom ≫ (G.homologyHom j).hom :=
  rfl

@[simp]
theorem comp_cyclesHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).cyclesHom j).hom =
      (F.cyclesHom j).hom ≫ (G.cyclesHom j).hom :=
  rfl

@[simp]
theorem comp_termHom_hom {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) (j : ℕ) :
    ((Hom.comp P Q g F G).termHom j).hom =
      (F.termHom j).hom ≫ (G.termHom j).hom :=
  rfl

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. If g=g′, a comparison F over g transports to a
comparison over g′. This identification leaves the underlying boundary, homology, cycle and term
chain maps, and hence the induced term-complex and bicomplex maps, unchanged. -/
def cast {P : CartanEilenbergResolution L}
    {Q : CartanEilenbergResolution L'} {g g' : L ⟶ L'}
    (F : Hom P Q g) (h : g = g') : Hom P Q g' :=
  h ▸ F

@[simp]
theorem cast_rfl (F : Hom P Q g) : F.cast rfl = F :=
  rfl

@[simp]
theorem cast_cast {g' g'' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (h' : g' = g'') : (F.cast h).cast h' = F.cast (h.trans h') := by
  cases h
  cases h'
  rfl

@[simp]
theorem cast_boundaryHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).boundaryHom j).hom = (F.boundaryHom j).hom := by
  cases h
  rfl

@[simp]
theorem cast_homologyHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).homologyHom j).hom = (F.homologyHom j).hom := by
  cases h
  rfl

@[simp]
theorem cast_cyclesHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).cyclesHom j).hom = (F.cyclesHom j).hom := by
  cases h
  rfl

@[simp]
theorem cast_termHom_hom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) :
    ((F.cast h).termHom j).hom = (F.termHom j).hom := by
  cases h
  rfl

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For g=g′, the boundary
endpoint of the transported comparison is the original boundary-resolution morphism identified
over the equal outgoing-boundary maps of g and g′. -/
theorem cast_boundaryHom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) : (F.cast h).boundaryHom j =
      (F.boundaryHom j).cast
        (congrArg (fun k => boundaryFromMap k j) h) := by
  ext
  simp

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For g=g′, the homology
endpoint of the transported comparison is the original projective-resolution morphism identified
over the equal maps Hⱼ(g) and Hⱼ(g′). -/
theorem cast_homologyHom {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g')
    (j : ℕ) : (F.cast h).homologyHom j =
      (F.homologyHom j).cast
        (congrArg (fun k => homologyMap k j) h) := by
  ext
  simp

@[simp]
theorem termComplexHom_cast {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g') :
    (F.cast h).termComplexHom = F.termComplexHom := by
  cases h
  rfl

@[simp]
theorem bicomplexHom_cast {g' : L ⟶ L'} (F : Hom P Q g) (h : g = g') :
    (F.cast h).bicomplexHom = F.bicomplexHom := by
  cases h
  rfl

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution. The identity
comparison over id_L induces the identity map of P.termComplex. -/
@[simp]
theorem termComplexHom_id (P : CartanEilenbergResolution L) :
    (Hom.id P).termComplexHom = 𝟙 P.termComplex := by
  ext j
  simp

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For a comparison G : Q → R
over h : L′ → L″, the term-complex map of the composite is G.termComplexHom ∘ F.termComplexHom. -/
@[simp]
theorem termComplexHom_comp {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) :
    (Hom.comp P Q g F G).termComplexHom =
      F.termComplexHom ≫ G.termComplexHom := by
  ext j
  simp

/-- Let C be abelian and P a Cartan–Eilenberg resolution of a nonnegative complex L. Its identity
comparison induces the identity map of P.bicomplex. -/
@[simp]
theorem bicomplexHom_id (P : CartanEilenbergResolution L) :
    (Hom.id P).bicomplexHom = 𝟙 P.bicomplex := by
  ext a j
  simp

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For a comparison G : Q → R
over h : L′ → L″, the bicomplex map of the composite equals G.bicomplexHom ∘ F.bicomplexHom. -/
@[simp]
theorem bicomplexHom_comp {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    (F : Hom P Q g) (G : Hom Q R h) :
    (Hom.comp P Q g F G).bicomplexHom = F.bicomplexHom ≫ G.bicomplexHom := by
  ext a j
  simp

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. Composing the identity
comparison of P with F gives F, after identifying id_L followed by g with g. -/
theorem id_comp (F : Hom P Q g) :
    (Hom.comp P P (𝟙 L) (Hom.id P) F).cast (Category.id_comp g) = F := by
  ext j <;> simp

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. Composing F with the identity
comparison of Q gives F, after identifying g followed by id_L′ with g. -/
theorem comp_id (F : Hom P Q g) :
    (Hom.comp P Q g F (Hom.id Q)).cast (Category.comp_id g) = F := by
  ext j <;> simp

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. Let F be a comparison of P and Q over g, with boundary,
homology, cycle and term resolution maps in each original degree. For comparisons G : Q → R over
h and H : R → S over k, the two parenthesizations of the three-comparison composite agree after
the canonical equality (k ∘ h) ∘ g=k ∘ (h ∘ g). -/
theorem assoc {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''}
    {L''' : ChainComplex C ℕ} {S : CartanEilenbergResolution L'''}
    {k : L'' ⟶ L'''} (F : Hom P Q g) (G : Hom Q R h) (H : Hom R S k) :
    (Hom.comp P R (g ≫ h) (Hom.comp P Q g F G) H).cast
        (Category.assoc g h k) =
      Hom.comp P Q g F (Hom.comp Q R h G H) := by
  ext j <;> simp

end Hom

/-- Let C be abelian, L,L′ nonnegative chain complexes, P and Q chosen Cartan–Eilenberg resolutions
of L and L′, and g : L → L′ a chain map. There exists a comparison of P and Q over g. The
boundary and homology projective-resolution lifts and the two horseshoe middle maps are chosen,
so this asserts existence rather than a canonical strict comparison. -/
theorem nonempty_hom : Nonempty (Hom P Q g) := by
  let beta (j : ℕ) :
      ProjectiveResolution.Hom (P.boundaryResolution j)
        (Q.boundaryResolution j) (boundaryFromMap g j) :=
    ProjectiveResolution.liftHom (boundaryFromMap g j)
      (P.boundaryResolution j) (Q.boundaryResolution j)
  let eta (j : ℕ) :
      ProjectiveResolution.Hom (P.homologyResolution j)
        (Q.homologyResolution j) (homologyMap g j) :=
    ProjectiveResolution.liftHom (homologyMap g j)
      (P.homologyResolution j) (Q.homologyResolution j)
  have hZ (j : ℕ) : Nonempty (ProjectiveResolution.HorseshoeData.Hom
      (H := P.cyclesHorseshoe j) (H' := Q.cyclesHorseshoe j)
      (φ := boundaryCyclesHomologyMap g j)
      (u := beta (j + 1)) (w := eta j)) :=
    ProjectiveResolution.HorseshoeData.nonempty_hom
      (hS := L.boundaryCyclesHomologyShortExact j)
      (hS' := L'.boundaryCyclesHomologyShortExact j)
      (P₁ := P.boundaryResolution (j + 1))
      (P₃ := P.homologyResolution j)
      (P₁' := Q.boundaryResolution (j + 1))
      (P₃' := Q.homologyResolution j)
      (H := P.cyclesHorseshoe j) (H' := Q.cyclesHorseshoe j)
      (sH := P.cyclesSpec j) (sH' := Q.cyclesSpec j)
      (φ := boundaryCyclesHomologyMap g j)
      (u := beta (j + 1)) (w := eta j)
  let zeta (j : ℕ) := (hZ j).some
  have hT (j : ℕ) : Nonempty (ProjectiveResolution.HorseshoeData.Hom
      (H := P.termHorseshoe j) (H' := Q.termHorseshoe j)
      (φ := cyclesTermBoundaryMap g j)
      (u := (zeta j).toProjectiveResolutionHom) (w := beta j)) :=
    ProjectiveResolution.HorseshoeData.nonempty_hom
      (hS := L.cyclesTermBoundaryShortExact j)
      (hS' := L'.cyclesTermBoundaryShortExact j)
      (P₁ := (P.cyclesHorseshoe j).middle)
      (P₃ := P.boundaryResolution j)
      (P₁' := (Q.cyclesHorseshoe j).middle)
      (P₃' := Q.boundaryResolution j)
      (H := P.termHorseshoe j) (H' := Q.termHorseshoe j)
      (sH := P.termSpec j) (sH' := Q.termSpec j)
      (φ := cyclesTermBoundaryMap g j)
      (u := (zeta j).toProjectiveResolutionHom) (w := beta j)
  let tau (j : ℕ) := (hT j).some
  exact ⟨⟨beta, eta, zeta, tau⟩⟩

end CartanEilenbergResolution

end HomologicalComplex

end
