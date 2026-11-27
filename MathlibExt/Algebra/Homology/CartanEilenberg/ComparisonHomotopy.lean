/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Comparison
public import MathlibExt.Algebra.Homology.CartanEilenberg.Existence
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Homotopy uniqueness of Cartan–Eilenberg comparisons

Let C be abelian and let P,Q be Cartan–Eilenberg resolutions over a chain map g : L → L′. Any
two comparisons over g admit compatible homotopies on their boundary, homology, cycle and term
resolution maps. Compatibility with the two horseshoe rows assembles these into a bicomplex
homotopy in resolution degree, whose components are chain maps in original degree.

Consequently the comparison determines a canonical homotopy-category morphism. Two resolutions
of the same complex give homotopy-equivalent bicomplexes. If every object of C has a projective
resolution, choosing Cartan–Eilenberg resolutions gives a functor from nonnegative complexes to
the homotopy category of chain complexes of chain complexes.
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

namespace Hom

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. A comparison
homotopy specifies homotopies between all four resolution-map families, commuting with the cycle
and term horseshoe inclusions and projections. In degree j, cycle inclusion compatibility uses
the boundary homotopy in degree j+1; term projection compatibility uses boundary degree j. -/
structure ComparisonHomotopy (F G : Hom P Q g) where
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For each j, the boundary component is a chain homotopy between F and G on the
resolutions of the outgoing boundary object Bⱼ⁽out⁾. -/
  boundaryHomotopy (j : ℕ) :
    Homotopy (F.boundaryHom j).hom (G.boundaryHom j).hom
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For each j, the homology component is a chain homotopy between the two lifts
covering Hⱼ(g), on the chosen resolutions of Hⱼ(L) and Hⱼ(L′). -/
  homologyHomotopy (j : ℕ) :
    Homotopy (F.homologyHom j).hom (G.homologyHom j).hom
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For each j, the cycle component is a chain homotopy between the two strict
cycle-horseshoe comparison maps. -/
  cyclesHomotopy (j : ℕ) :
    Homotopy (F.cyclesHom j).hom (G.cyclesHom j).hom
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For every j,a,b ∈ ℕ, the cycle homotopy component commutes with the cycle-horseshoe
inclusions: Θ.cyclesⱼ(a,b) ∘ i_P(a)=i_Q(b) ∘ Θ.boundaryⱼ₊₁(a,b). -/
  cycles_comp_i (j a b : ℕ) :
    (P.cyclesHorseshoe j).i.f a ≫ (cyclesHomotopy j).hom a b =
      (boundaryHomotopy (j + 1)).hom a b ≫ (Q.cyclesHorseshoe j).i.f b
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For every j,a,b ∈ ℕ, projection from the cycle horseshoe commutes with the
homotopies: p_Q(b) ∘ Θ.cyclesⱼ(a,b)=Θ.homologyⱼ(a,b) ∘ p_P(a). -/
  cycles_comp_p (j a b : ℕ) :
    (cyclesHomotopy j).hom a b ≫ (Q.cyclesHorseshoe j).p.f b =
      (P.cyclesHorseshoe j).p.f a ≫ (homologyHomotopy j).hom a b
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For each j, the term component is a chain homotopy between F and G on the chosen
projective term resolutions of Lⱼ and L′ⱼ. -/
  termHomotopy (j : ℕ) :
    Homotopy (F.termHom j).hom (G.termHom j).hom
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For every j,a,b ∈ ℕ, the term homotopy commutes with the term-horseshoe cycle
inclusions: Θ.termⱼ(a,b) ∘ i_P(a)=i_Q(b) ∘ Θ.cyclesⱼ(a,b). -/
  term_comp_i (j a b : ℕ) :
    (P.termHorseshoe j).i.f a ≫ (termHomotopy j).hom a b =
      (cyclesHomotopy j).hom a b ≫ (Q.termHorseshoe j).i.f b
  /-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For every j,a,b ∈ ℕ, the term-horseshoe projection satisfies p_Q(b) ∘
Θ.termⱼ(a,b)=Θ.boundaryⱼ(a,b) ∘ p_P(a). -/
  term_comp_p (j a b : ℕ) :
    (termHomotopy j).hom a b ≫ (Q.termHorseshoe j).p.f b =
      (P.termHorseshoe j).p.f a ≫ (boundaryHomotopy j).hom a b

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. There exists
a comparison homotopy between F and G, simultaneously on boundary, homology, cycle and term
resolutions and compatible with both horseshoe rows. -/
theorem nonempty_comparisonHomotopy (F G : Hom P Q g) :
    Nonempty (ComparisonHomotopy P Q g F G) := by
  let βH (j : ℕ) := (F.boundaryHom j).homotopy (G.boundaryHom j)
  let ηH (j : ℕ) := (F.homologyHom j).homotopy (G.homologyHom j)
  have hζ : ∀ j : ℕ, ∃ h : Homotopy (F.cyclesHom j).hom (G.cyclesHom j).hom,
      (∀ a b : ℕ, (P.cyclesHorseshoe j).i.f a ≫ h.hom a b =
        (βH (j + 1)).hom a b ≫ (Q.cyclesHorseshoe j).i.f b) ∧
      ∀ a b : ℕ, h.hom a b ≫ (Q.cyclesHorseshoe j).p.f b =
        (P.cyclesHorseshoe j).p.f a ≫ (ηH j).hom a b := fun j =>
    CategoryTheory.ProjectiveResolution.HorseshoeData.Hom.nonempty_homotopy
      (P.cyclesSpec j) (Q.cyclesSpec j) (βH (j + 1)) (ηH j) (F.cyclesHom j)
      (G.cyclesHom j)
  choose ζH hζe using hζ
  have hτ : ∀ j : ℕ, ∃ h : Homotopy (F.termHom j).hom (G.termHom j).hom,
      (∀ a b : ℕ, (P.termHorseshoe j).i.f a ≫ h.hom a b =
        (ζH j).hom a b ≫ (Q.termHorseshoe j).i.f b) ∧
      ∀ a b : ℕ, h.hom a b ≫ (Q.termHorseshoe j).p.f b =
        (P.termHorseshoe j).p.f a ≫ (βH j).hom a b := fun j =>
    CategoryTheory.ProjectiveResolution.HorseshoeData.Hom.nonempty_homotopy
      (P.termSpec j) (Q.termSpec j) (ζH j) (βH j) (F.termHom j) (G.termHom j)
  choose τH hτe using hτ
  exact ⟨{ boundaryHomotopy := βH,
            homologyHomotopy := ηH,
            cyclesHomotopy := ζH,
            cycles_comp_i := fun j => (hζe j).1,
            cycles_comp_p := fun j => (hζe j).2,
            termHomotopy := τH,
            term_comp_i := fun j => (hτe j).1,
            term_comp_p := fun j => (hτe j).2 }⟩

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. In every
original degree j, the boundary-resolution chain maps of F and G are homotopic. -/
theorem nonempty_boundaryHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.boundaryHom j).hom (G.boundaryHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.boundaryHomotopy j

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. In every
original degree j, the homology-resolution lifts of F and G are homotopic. -/
theorem nonempty_homologyHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.homologyHom j).hom (G.homologyHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.homologyHomotopy j

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. In every
original degree j, the cycle-horseshoe comparison chain maps of F and G are homotopic. -/
theorem nonempty_cyclesHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.cyclesHom j).hom (G.cyclesHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.cyclesHomotopy j

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. In every
original degree j, the term-horseshoe comparison chain maps of F and G are homotopic. -/
theorem nonempty_termHomotopy (F G : Hom P Q g) (j : ℕ) :
    Nonempty (Homotopy (F.termHom j).hom (G.termHom j).hom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ => Θ.termHomotopy j

namespace ComparisonHomotopy

variable {F G : Hom P Q g} (Θ : ComparisonHomotopy P Q g F G)

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. For resolution degrees a,b, the term-homotopy components Θ.termⱼ(a,b) assemble in
original degree j to a chain map P.bicomplex.Xₐ → Q.bicomplex.X_b. The map vanishes off the
successor diagonal b=a+1. -/
noncomputable def bicomplexHomotopyHom (a b : ℕ) :
    P.bicomplex.X a ⟶ Q.bicomplex.X b :=
  ChainComplex.ofHom (fun j => (Θ.termHomotopy j).hom a b) (fun j => by
    by_cases hb : a + 1 = b
    · subst hb
      rw [Q.bicomplex_d₂, P.bicomplex_d₂, Q.termDifferential_eq j,
        P.termDifferential_eq j]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [reassoc_of% (Θ.term_comp_p (j + 1) a (a + 1)),
        ← reassoc_of% (Θ.cycles_comp_i j a (a + 1)),
        ← Θ.term_comp_i j a (a + 1)]
    · have hz1 : (Θ.termHomotopy (j + 1)).hom a b = 0 :=
        (Θ.termHomotopy (j + 1)).zero a b hb
      have hz2 : (Θ.termHomotopy j).hom a b = 0 :=
        (Θ.termHomotopy j).zero a b hb
      rw [hz1, hz2]
      simp)

@[simp]
theorem bicomplexHomotopyHom_f (a b j : ℕ) :
    (bicomplexHomotopyHom P Q g Θ a b).f j = (Θ.termHomotopy j).hom a b :=
  rfl

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. Let Θ be a
comparison homotopy, consisting of compatible boundary, homology, cycle and term resolution
homotopies. These component maps give a homotopy F.bicomplexHom ≃ G.bicomplexHom in resolution
degree, regarding each bicomplex as a chain complex of original-degree chain complexes. -/
noncomputable def bicomplexHomotopy :
    Homotopy F.bicomplexHom G.bicomplexHom where
  hom a b := bicomplexHomotopyHom P Q g Θ a b
  zero a b h := by
    ext j
    simp only [bicomplexHomotopyHom_f, HomologicalComplex.zero_f_apply]
    exact (Θ.termHomotopy j).zero a b h
  comm a := by
    cases a with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
        ext j
        have hc := (Θ.termHomotopy j).comm 0
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
          at hc
        simp only [zero_add] at hc
        simp only [bicomplexHomotopyHom_f, HomologicalComplex.add_f_apply,
          HomologicalComplex.comp_f, Hom.bicomplexHom_f_f,
          CartanEilenbergResolution.bicomplex_d₁, zero_add]
        exact hc
    | succ a =>
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        ext j
        have hc := (Θ.termHomotopy j).comm (a + 1)
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
          at hc
        simp only [bicomplexHomotopyHom_f, HomologicalComplex.add_f_apply,
          HomologicalComplex.comp_f, Hom.bicomplexHom_f_f,
          CartanEilenbergResolution.bicomplex_d₁]
        exact hc

@[simp]
theorem bicomplexHomotopy_hom_f (a b j : ℕ) :
    ((bicomplexHomotopy P Q g Θ).hom a b).f j = (Θ.termHomotopy j).hom a b :=
  rfl

end ComparisonHomotopy

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. The induced
bicomplex maps are homotopic in the resolution direction, with homotopy components chain maps in
the original degree. -/
theorem nonempty_bicomplexHomotopy (F G : Hom P Q g) :
    Nonempty (Homotopy F.bicomplexHom G.bicomplexHom) :=
  (nonempty_comparisonHomotopy P Q g F G).map fun Θ =>
    ComparisonHomotopy.bicomplexHomotopy P Q g Θ

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. For a comparison F over g, its bicomplex map determines a morphism
[P.bicomplex] → [Q.bicomplex] in the homotopy category of ℕ-indexed chain complexes of ℕ-indexed
chain complexes, with the outer index the resolution degree. -/
noncomputable def homotopyClass (F : Hom P Q g) :
    (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex ⟶
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj Q.bicomplex :=
  (HomotopyCategory.quotient (ChainComplex C ℕ)
    (ComplexShape.down ℕ)).map F.bicomplexHom

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Let F,G be comparisons of P and Q over the same map g. The induced
morphisms [P.bicomplex] → [Q.bicomplex] in the resolution-direction homotopy category are equal,
so this morphism does not depend on the comparison choice. -/
theorem homotopyClass_eq (F G : Hom P Q g) :
    F.homotopyClass = G.homotopyClass :=
  HomotopyCategory.eq_of_homotopy _ _
    (Classical.choice (nonempty_bicomplexHomotopy P Q g F G))

end Hom

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Choosing any comparison over g defines the same morphism
[P.bicomplex] → [Q.bicomplex] in the homotopy category of chain complexes of chain complexes. -/
noncomputable def homotopyClassMap :
    (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex ⟶
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj Q.bicomplex :=
  (Classical.choice (nonempty_hom P Q g)).homotopyClass

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. Every comparison F over g represents the canonical morphism
[P.bicomplex] → [Q.bicomplex]: homotopyClassMap(P,Q,g)=[F.bicomplexHom]. -/
theorem homotopyClassMap_eq (F : Hom P Q g) :
    homotopyClassMap P Q g = F.homotopyClass :=
  Hom.homotopyClass_eq P Q g _ F

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution. The canonical
homotopy-category map of id_L is the identity of [P.bicomplex]. -/
theorem homotopyClassMap_id (P : CartanEilenbergResolution L) :
    homotopyClassMap P P (𝟙 L) =
      𝟙 ((HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex) := by
  rw [homotopyClassMap_eq P P (𝟙 L) (Hom.id P)]
  simp [Hom.homotopyClass]

/-- Let C be abelian, L,L′ chain complexes indexed by ℕ, P and Q chosen Cartan–Eilenberg
resolutions, and g : L → L′. For h : L′ → L″ and a Cartan–Eilenberg resolution R of L″, the
canonical homotopy map of h ∘ g is the map of g followed by the map of h. -/
theorem homotopyClassMap_comp {L'' : ChainComplex C ℕ}
    {R : CartanEilenbergResolution L''} {h : L' ⟶ L''} :
    homotopyClassMap P R (g ≫ h) =
      homotopyClassMap P Q g ≫ homotopyClassMap Q R h := by
  let F : Hom P Q g := Classical.choice (nonempty_hom P Q g)
  let G : Hom Q R h := Classical.choice (nonempty_hom Q R h)
  have eF : homotopyClassMap P Q g = F.homotopyClass :=
    homotopyClassMap_eq P Q g F
  have eG : homotopyClassMap Q R h = G.homotopyClass :=
    homotopyClassMap_eq Q R h G
  rw [homotopyClassMap_eq P R (g ≫ h) (Hom.comp P Q g F G), eF, eG]
  simp [Hom.homotopyClass]

/-- Let C be abelian, L a nonnegative complex and P,Q two Cartan–Eilenberg resolutions of L. Their
bicomplexes are homotopy equivalent in resolution degree, by comparisons over id_L in both
directions. -/
noncomputable def bicomplexHomotopyEquiv {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    HomotopyEquiv P.bicomplex Q.bicomplex where
  hom := (Classical.choice (nonempty_hom P Q (𝟙 L))).bicomplexHom
  inv := (Classical.choice (nonempty_hom Q P (𝟙 L))).bicomplexHom
  homotopyHomInvId := by
    have h := Classical.choice (Hom.nonempty_bicomplexHomotopy P P (𝟙 L)
      ((Hom.comp P Q (𝟙 L) (Classical.choice (nonempty_hom P Q (𝟙 L)))
        (Classical.choice (nonempty_hom Q P (𝟙 L)))).cast
          (Category.id_comp (𝟙 L)))
      (Hom.id P))
    simpa using h
  homotopyInvHomId := by
    have h := Classical.choice (Hom.nonempty_bicomplexHomotopy Q Q (𝟙 L)
      ((Hom.comp Q P (𝟙 L) (Classical.choice (nonempty_hom Q P (𝟙 L)))
        (Classical.choice (nonempty_hom P Q (𝟙 L)))).cast
          (Category.id_comp (𝟙 L)))
      (Hom.id Q))
    simpa using h

/-- Let C be abelian and P,Q Cartan–Eilenberg resolutions of the same nonnegative complex L. The
homotopy equivalence of their bicomplexes gives a canonical isomorphism [P.bicomplex] ≅
[Q.bicomplex] in the resolution-direction homotopy category. -/
noncomputable def homotopyCategoryIso {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex ≅
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj Q.bicomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (bicomplexHomotopyEquiv P Q)

/-- Let C be abelian and P,Q Cartan–Eilenberg resolutions of L. The forward map of [P.bicomplex] ≅
[Q.bicomplex] is the canonical homotopy-category map over id_L from P to Q. -/
@[simp]
theorem homotopyCategoryIso_hom {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    (homotopyCategoryIso P Q).hom = homotopyClassMap P Q (𝟙 L) :=
  rfl

/-- Let C be abelian and P,Q Cartan–Eilenberg resolutions of L. The inverse map of [P.bicomplex] ≅
[Q.bicomplex] is the canonical homotopy-category map over id_L from Q to P. -/
@[simp]
theorem homotopyCategoryIso_inv {L : ChainComplex C ℕ}
    (P Q : CartanEilenbergResolution L) :
    (homotopyCategoryIso P Q).inv = homotopyClassMap Q P (𝟙 L) :=
  rfl

end CartanEilenbergResolution

section Functor

variable [HasProjectiveResolutions C]

/-- Let C be abelian and assume every object has a projective resolution. Choosing Cartan–Eilenberg
resolutions defines a functor from nonnegative chain complexes in C to the homotopy category of
nonnegative chain complexes of nonnegative chain complexes. It sends L to its resolution
bicomplex, indexed first by resolution degree, and g to the homotopy class of any comparison
over g. -/
noncomputable def cartanEilenbergResolutions (C : Type u) [Category.{v} C]
    [Abelian C] [HasProjectiveResolutions C] :
    ChainComplex C ℕ ⥤
      HomotopyCategory (ChainComplex C ℕ) (ComplexShape.down ℕ) where
  obj L := (HomotopyCategory.quotient (ChainComplex C ℕ)
      (ComplexShape.down ℕ)).obj (CartanEilenbergResolution.of L).bicomplex
  map f := CartanEilenbergResolution.homotopyClassMap
    (CartanEilenbergResolution.of _) (CartanEilenbergResolution.of _) f
  map_id L := CartanEilenbergResolution.homotopyClassMap_id
    (CartanEilenbergResolution.of L)
  map_comp f g := CartanEilenbergResolution.homotopyClassMap_comp
    (CartanEilenbergResolution.of _) (CartanEilenbergResolution.of _) f
    (R := CartanEilenbergResolution.of _) (h := g)

/-- Let C be abelian and assume every object has a projective resolution. For every nonnegative
complex L, the resolution functor sends L to the homotopy class of the bicomplex of its chosen
Cartan–Eilenberg resolution. -/
theorem cartanEilenbergResolutions_obj (L : ChainComplex C ℕ) :
    (cartanEilenbergResolutions C).obj L =
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj (CartanEilenbergResolution.of L).bicomplex :=
  rfl

/-- Let C be abelian and assume every object has a projective resolution. For g : L → L′, every
comparison F between the chosen Cartan–Eilenberg resolutions over g represents the functor's
morphism: its value is [F.bicomplexHom]. -/
theorem cartanEilenbergResolutions_map {L L' : ChainComplex C ℕ}
    (g : L ⟶ L')
    (F : CartanEilenbergResolution.Hom (CartanEilenbergResolution.of L)
      (CartanEilenbergResolution.of L') g) :
    (cartanEilenbergResolutions C).map g =
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).map F.bicomplexHom :=
  CartanEilenbergResolution.homotopyClassMap_eq _ _ _ F

/-- Let C be abelian and assume every object has a projective resolution. For every L and every
Cartan–Eilenberg resolution P of L, the chosen value of the resolution functor is canonically
isomorphic in the homotopy category to [P.bicomplex]. -/
noncomputable def cartanEilenbergResolutions_obj_iso (L : ChainComplex C ℕ)
    (P : CartanEilenbergResolution L) :
    (cartanEilenbergResolutions C).obj L ≅
      (HomotopyCategory.quotient (ChainComplex C ℕ)
        (ComplexShape.down ℕ)).obj P.bicomplex :=
  CartanEilenbergResolution.homotopyCategoryIso
    (CartanEilenbergResolution.of L) P

end Functor

end HomologicalComplex

end
