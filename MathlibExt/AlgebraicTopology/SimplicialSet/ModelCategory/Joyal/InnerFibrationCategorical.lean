/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Descent
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration

/-!
# Boundary lifting and pre-fibrant descent comparisons

For simplicial maps in universe u, boundary right lifting is equivalent to lifting each
∂Δ[n]→Δ[n]. Surjectivity on vertices supplies dimension zero, and for a vertex-bijective map the
remaining tests are exactly the positive dimensions.

Pullback squares transport boundary lifting and vertex bijectivity. The under-slice comparison
X_{x/}→S_{p(x)/}×_S X has the under-slice postcomposition and forgetful maps as its two
projections. Requiring all left mapping-space comparisons of p to lift boundaries gives the
mapping-space trivial-fibration predicate, with identity, composition and vertex-surjectivity
laws.

Inner-anodyne descent of p:X→S along f:S→T means there are Y, an inner fibration q:Y→T and an
inner-anodyne g:X→Y forming the pullback square g≫q=p≫f. A pre-fibrant descent datum
additionally requires an inner-anodyne, vertex-bijective f:S→T with pre-fibrant T. A uniform
replacement chooses the same f for every inner fibration over S.

References: D. Stevenson, Notes on the Joyal model structure, arXiv:1810.05233; J. Lurie, Higher
Topos Theory; A. Campbell, A counterexample in quasi-category theory, arXiv:1904.04965.

Pre-fibrancy means that two-dimensional inner horns fill and higher inner horns with constant
zeroth face fill.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y S T : SSet.{u}}

/-!
## Boundary lifting in every dimension

Right lifting against the boundary family means that each ∂Δ[n]→Δ[n] has the lifting property
with p. In dimension zero the empty boundary means a lift is a preimage of a vertex.
-/

/-- For p:X→S in simplicial-set universe u, right lifting against the boundary family is equivalent
to HasLiftingProperty(∂Δ[n]→Δ[n],p) for every n∈ℕ. -/
theorem modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary
    (p : X ⟶ S) :
    modelCategoryQuillen.I.rlp p ↔
      ∀ n : ℕ, HasLiftingProperty (boundary n).ι p := by
  refine ⟨fun hp ↦ hasLiftingProperty_boundary_of_rlp_I hp, fun h ↦ ?_⟩
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact h n

/-!
## Dimension zero from vertex surjectivity

A map surjective on vertices lifts the zero-dimensional boundary ∅→Δ[0]. For a vertex-bijective
map, all remaining boundary lifting tests have positive dimension.
-/

/-- For p:X→S in universe u, if p₀:X₀→S₀ is surjective, then p has the lifting property against
∂Δ[0]→Δ[0]. The source ∂Δ[0] is empty, and a lift chooses a preimage of the bottom vertex. -/
theorem hasLiftingProperty_boundary_zero_of_surjective_app_zero
    {p : X ⟶ S} (hf : Function.Surjective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (boundary 0).ι p where
  sq_hasLift {top bottom} sq := by
    obtain ⟨x, hx⟩ := hf (yonedaEquiv bottom)
    have hinit : IsInitial ((boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) :=
      (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
        (Subcomplex.eqToIso boundary_zero).symm
    refine CommSq.HasLift.mk' ⟨yonedaEquiv.symm x, hinit.hom_ext _ _, ?_⟩
    rw [yonedaEquiv_symm_comp, hx, Equiv.symm_apply_apply]

/-- For p:X→S in universe u, bijectivity of p₀:X₀→S₀ implies the lifting property against the
empty-boundary inclusion ∂Δ[0]→Δ[0]. -/
theorem hasLiftingProperty_boundary_zero_of_bijective_app_zero
    {p : X ⟶ S} (hf : Function.Bijective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (boundary 0).ι p :=
  hasLiftingProperty_boundary_zero_of_surjective_app_zero hf.2

/-- For p:X→S in universe u with bijective p₀:X₀→S₀, right lifting against all boundaries is
equivalent to lifting ∂Δ[n]→Δ[n] for every n≥1. Vertex bijectivity supplies the n=0 test. -/
theorem modelCategoryQuillen_I_rlp_iff_of_bijective_app_zero {p : X ⟶ S}
    (hf : Function.Bijective (p.app (op ⦋0⦌))) :
    modelCategoryQuillen.I.rlp p ↔
      ∀ n : ℕ, 1 ≤ n → HasLiftingProperty (boundary n).ι p := by
  rw [modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary]
  refine ⟨fun h n _ ↦ h n, fun h n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hasLiftingProperty_boundary_zero_of_bijective_app_zero hf
  · exact h n hn

/-!
## Transport across a pullback square

In the square X→Y, X→S, Y→T, S→T, write its maps as g,p,q,f, with g≫q=p≫f. Boundary lifting
pulls back from q to p; categorical equivalence and vertex bijectivity transport under the
stated conditions on the other three maps.
-/

/-- Let X,Y,S,T be simplicial sets in universe u and g:X→Y, p:X→S, q:Y→T, f:S→T form a pullback
square, so g≫q=p≫f. If q lifts against all ∂Δ[n]→Δ[n], then its pullback p also lifts against
that entire boundary family. -/
theorem modelCategoryQuillen_I_rlp_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hq : modelCategoryQuillen.I.rlp q) :
    modelCategoryQuillen.I.rlp p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hq

/-- Let X,Y,S,T be simplicial sets in universe u and g:X→Y, p:X→S, q:Y→T, f:S→T form a pullback
square, so g≫q=p≫f. If g,f,p are categorical equivalences, then q is a categorical equivalence.
Here categorical means that all quasicategory-target precomposition functors on homotopy
categories are equivalences. -/
theorem categoricalEquivalences_right_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hg : categoricalEquivalences g) (hf : categoricalEquivalences f)
    (hp : categoricalEquivalences p) : categoricalEquivalences q := by
  have hcomp : categoricalEquivalences (g ≫ q) := by
    rw [sq.w]
    exact categoricalEquivalences.comp_mem _ _ hp hf
  exact categoricalEquivalences.of_precomp g q hg hcomp

/-- Let X,Y,S,T be simplicial sets in universe u and g:X→Y, p:X→S, q:Y→T, f:S→T form a pullback
square, so g≫q=p≫f. If f₀:S₀→T₀ is bijective, then g₀:X₀→Y₀ is bijective. -/
theorem bijective_app_zero_fst_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    Function.Bijective (g.app (op ⦋0⦌)) := by
  have sq0 := sq.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))
  have hfI : IsIso (((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)).map f) := by
    rw [isIso_iff_bijective]
    exact hf
  have hgI := sq0.isIso_fst_of_isIso (inst := hfI)
  exact (isIso_iff_bijective _).mp hgI

/-- Let X,Y,S,T be simplicial sets in universe u and g:X→Y, p:X→S, q:Y→T, f:S→T form a pullback
square, so g≫q=p≫f. If f₀:S₀→T₀ and p₀:X₀→S₀ are bijective, then q₀:Y₀→T₀ is bijective. -/
theorem bijective_app_zero_right_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hf : Function.Bijective (f.app (op ⦋0⦌)))
    (hp : Function.Bijective (p.app (op ⦋0⦌))) :
    Function.Bijective (q.app (op ⦋0⦌)) := by
  have hg : Function.Bijective (g.app (op ⦋0⦌)) :=
    bijective_app_zero_fst_of_isPullback sq hf
  have hcomp : Function.Bijective ((g ≫ q).app (op ⦋0⦌)) := by
    rw [sq.w, NatTrans.comp_app]
    exact hf.comp hp
  have hqapp : (g ≫ q).app (op ⦋0⦌) = q.app (op ⦋0⦌) ∘ g.app (op ⦋0⦌) := rfl
  rw [hqapp] at hcomp
  refine ⟨fun a b hab ↦ ?_, Function.Surjective.of_comp hcomp.2⟩
  obtain ⟨a', rfl⟩ := hg.2 a
  obtain ⟨b', rfl⟩ := hg.2 b
  exact congrArg (g.app (op ⦋0⦌)) (hcomp.1 hab)

/-!
## The comparison of under-slices

For x:Δ[0]→X and p:X→S, the comparison X_{x/}→S_{p(x)/}×_S X is induced by postcomposition on
under-slices and by forgetting the source under-slice simplex.
-/

/-- For p:X→S in universe u and vertex map x:Δ[0]→X, define c:X_{x/}→S_{x≫p/}×_S X. Its first
projection is postcomposition of under-slice simplices by p, and its second projection forgets
the source under-slice simplex. -/
noncomputable def sliceUnderComparison {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnder X x ⟶ pullback (sliceUnder.proj S (x ≫ p)) p :=
  pullback.lift (sliceUnder.map X x p) (sliceUnder.proj X x)
    (sliceUnder.map_proj X x p)

/-- For p:X→S in universe u and x:Δ[0]→X, the comparison c:X_\{x/\}→S_\{x≫p/\}×_S X satisfies
c≫pr₁=(p-induced map):X_\{x/\}→S_\{x≫p/\}. -/
@[reassoc (attr := simp)]
theorem sliceUnderComparison_fst {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnderComparison (p := p) x ≫
        pullback.fst (sliceUnder.proj S (x ≫ p)) p =
      sliceUnder.map X x p :=
  pullback.lift_fst _ _ _

/-- For p:X→S in universe u and x:Δ[0]→X, the comparison c:X_\{x/\}→S_\{x≫p/\}×_S X satisfies
c≫pr₂=proj_X:X_\{x/\}→X. -/
@[reassoc (attr := simp)]
theorem sliceUnderComparison_snd {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnderComparison (p := p) x ≫
        pullback.snd (sliceUnder.proj S (x ≫ p)) p =
      sliceUnder.proj X x :=
  pullback.lift_snd _ _ _

/-!
## Boundary lifting on left mapping spaces

For every pair a,b:Δ[0]→X, require the postcomposition map L_X(a,b)→L_S(a≫p,b≫p) to lift all
boundary inclusions. This condition contains identities and is closed under composition.
-/

/-- For p:X→S in universe u, define the mapping-space trivial-fibration condition to mean that every
L_X(a,b)→L_S(a≫p,b≫p), a,b:Δ[0]→X, has the right lifting property against all boundary
inclusions. The L symbols denote the left join-slice mapping-space models. -/
def MappingSpaceLeftTrivialFibration {X S : SSet.{u}} (p : X ⟶ S) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
    modelCategoryQuillen.I.rlp (mappingSpaceLeft.map X a b p)

/-- For any simplicial set X in universe u, every induced map L_X(a,b)→L_X(a,b) of id_X is an
identity and lifts all boundaries. Thus id_X satisfies the left mapping-space trivial-fibration
condition. -/
theorem mappingSpaceLeftTrivialFibration_id :
    MappingSpaceLeftTrivialFibration (𝟙 X) := by
  intro a b
  rw [mappingSpaceLeft.map_id]
  exact MorphismProperty.id_mem _ _

/-- For p:X→S and q:S→T in universe u, if every left mapping-space comparison of p and of q lifts
all boundaries, then the comparisons of p≫q also lift all boundaries. -/
theorem MappingSpaceLeftTrivialFibration.comp {p : X ⟶ S} {q : S ⟶ T}
    (hp : MappingSpaceLeftTrivialFibration p)
    (hq : MappingSpaceLeftTrivialFibration q) :
    MappingSpaceLeftTrivialFibration (p ≫ q) := by
  intro a b
  rw [mappingSpaceLeft.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (hp a b) (hq (a ≫ p) (b ≫ p))

/-- For p:X→S in universe u satisfying boundary lifting on every left mapping-space comparison, and
a,b:Δ[0]→X, the map L_X(a,b)₀→L_S(a≫p,b≫p)₀ is surjective. -/
theorem MappingSpaceLeftTrivialFibration.surjective_app_zero {p : X ⟶ S}
    (hp : MappingSpaceLeftTrivialFibration p)
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Surjective ((mappingSpaceLeft.map X a b p).app (op ⦋0⦌)) :=
  fun y ↦ exists_vertex_lift_of_rlp_I (hp a b) y

/-!
## Edge classes under categorical equivalences

A categorical equivalence is full and faithful on homotopy-category morphisms. When the source
is a quasicategory, a target edge between image vertices has an image-edge representative with
the same homotopy-class morphism.
-/

/-- For categorical f:X→S in universe u with X a quasicategory, vertices x,y of X and an edge
e′:f(x)→f(y) in S, there is an edge e:x→y in X whose image f(e) represents the same morphism as
e′ in ho(S). -/
theorem categoricalEquivalences.exists_edge_map_toHoHom_eq
    [Quasicategory X] {f : X ⟶ S} (hf : categoricalEquivalences f)
    {x y : X _⦋0⦌} (e' : Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : Edge x y, (e.map f).toHoHom = e'.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq e'

/-- For categorical f:X→S in universe u and edges e₁,e₂:x→y in X, equality of the image-edge
morphisms [f(e₁)]=[f(e₂)] in ho(S) implies [e₁]=[e₂] in ho(X). -/
theorem categoricalEquivalences.edge_map_toHoHom_injective
    {f : X ⟶ S} (hf : categoricalEquivalences f) {x y : X _⦋0⦌}
    {e₁ e₂ : Edge x y}
    (h : (e₁.map f).toHoHom = (e₂.map f).toHoHom) :
    e₁.toHoHom = e₂.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.edge_map_toHoHom_injective h

/-!
## Pre-fibrant descent data and uniform replacement

A datum for p selects one inner-anodyne, vertex-bijective f:S→T with pre-fibrant T and an
inner-anodyne pullback descent of p. Uniform replacement chooses T,f once for each S, before
quantifying over every inner fibration p over S.
-/

/-- For p:X→S in universe u, a pre-fibrant descent datum consists of T and f:S→T with f inner
anodyne and bijective on vertices, T pre-fibrant, and inner-anodyne descent of p along f.
Inner-anodyne descent of p:X→S along f:S→T means there are Y, an inner fibration q:Y→T and an
inner-anodyne g:X→Y forming the pullback square g≫q=p≫f. Pre-fibrancy means that two-dimensional
inner horns fill and higher inner horns with constant zeroth face fill. -/
def HasPreFibrantDescentDatum {X S : SSet.{u}} (p : X ⟶ S) : Prop :=
  ∃ (T : SSet.{u}) (f : S ⟶ T),
    innerAnodyneExtensions f ∧ IsPreFibrant T ∧
      Function.Bijective (f.app (op ⦋0⦌)) ∧
      SatisfiesInnerAnodyneDescent p f

/-- For an inner fibration p:X→S in universe u with S pre-fibrant, a pre-fibrant descent datum is
supplied by T=S, f=id_S, Y=X, q=p and g=id_X. The identity square is a pullback, and both
identity horizontal maps are inner anodyne. -/
theorem hasPreFibrantDescentDatum_of_isPreFibrant {p : X ⟶ S}
    [InnerFibration p] [IsPreFibrant S] :
    HasPreFibrantDescentDatum p :=
  ⟨S, 𝟙 S, innerAnodyneExtensions.id_mem S, inferInstance, by
      have h : ∀ x : S _⦋0⦌, (𝟙 S : S ⟶ S).app (op ⦋0⦌) x = x :=
        fun x ↦ by simp
      exact ⟨fun a b hab ↦ by rwa [h, h] at hab, fun b ↦ ⟨b, h b⟩⟩,
    satisfiesInnerAnodyneDescent_id p⟩

/-- In universe u, the uniform replacement property says that for each simplicial set S there exist
one pre-fibrant T and one inner-anodyne vertex-bijective f:S→T such that every inner fibration
p:X→S admits inner-anodyne descent along that same f. Inner-anodyne descent of p:X→S along f:S→T
means there are Y, an inner fibration q:Y→T and an inner-anodyne g:X→Y forming the pullback
square g≫q=p≫f. Pre-fibrancy means that two-dimensional inner horns fill and higher inner horns
with constant zeroth face fill. -/
def PreFibrantDescentReplacementExists : Prop :=
  ∀ S : SSet.{u}, ∃ (T : SSet.{u}) (f : S ⟶ T),
    innerAnodyneExtensions f ∧ IsPreFibrant T ∧
      Function.Bijective (f.app (op ⦋0⦌)) ∧
      ∀ {X : SSet.{u}} (p : X ⟶ S), InnerFibration p →
        SatisfiesInnerAnodyneDescent p f

/-- Assume the universe-u uniform replacement property: each S has one inner-anodyne
vertex-bijective map to a pre-fibrant target, along which every inner fibration descends. Then
each inner fibration p:X→S has a pre-fibrant descent datum. -/
theorem HasPreFibrantDescentDatum.of_replacementExists
    (h : PreFibrantDescentReplacementExists.{u}) {p : X ⟶ S}
    [InnerFibration p] : HasPreFibrantDescentDatum p := by
  obtain ⟨T, f, hfAnod, hT, hfBij, hdesc⟩ := h S
  exact ⟨T, f, hfAnod, hT, hfBij, hdesc p inferInstance⟩

end SSet

end
