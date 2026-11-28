/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Counit
public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairingAssociativity
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneousBasic
public import MathlibExt.CategoryTheory.Monoidal.ComonObjIso
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality

/-!
# Coassociative resolution diagonals and associative cup products

For a group `G`, the simplicial universal cover `EG` is a Cartesian comonoid: its diagonal
sends a simplex to two copies, and its counit sends every simplex to the unique element of the
tensor unit. Over a commutative ring `k`, linearization and the Alexander–Whitney map give a
coassociative diagonal on the standard resolution. Transport along the bar/standard comparison
gives the bar diagonal.

For representations `A,B,D` and degrees `p,q,r : ℕ`, the resulting bar-cochain pairing and
group-cohomology cup satisfy `e(α_*((x ∪ y) ∪ z)) = x ∪ (y ∪ z)`. The coefficient associator
is `α : (A ⊗ B) ⊗ D → A ⊗ (B ⊗ D)`, and `e` is the canonical degree identification for `(p +
q) + r = p + (q + r)`. The morphism identities also include the associator on the three input
cochain or cohomology modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable (G : Type u) [Group G]

/-- For a group `G`, the morphism `EG → 𝟙_` in simplicial `G`-sets sends every homogeneous simplex
`u : Fin (n + 1) → G` to `PUnit.unit`. The target is the constant simplicial one-point set
with trivial `G`-action. -/
def universalCoverCounit :
    classifyingSpaceUniversalCover G ⟶
      𝟙_ (SimplicialObject (Action (Type u) G)) where
  app _ :=
    { hom := ↾(fun _ => PUnit.unit)
      comm := fun _ => rfl }
  naturality := by
    intro X Y f
    ext x
    rfl

/-- For a group `G`, the simplicial universal cover `EG` has comonoid structure with
comultiplication `universalCoverDiagonal G : EG → EG ⊗ EG` and counit `universalCoverCounit G
: EG → 𝟙_`. These are the pointwise maps `u ↦ (u,u)` and `u ↦ PUnit.unit`, satisfying both
counit identities and coassociativity with the Cartesian associator. -/
@[instance_reducible]
noncomputable def universalCoverComonObj :
    ComonObj (classifyingSpaceUniversalCover G) where
  counit := universalCoverCounit G
  comul := universalCoverDiagonal G
  counit_comul := by
    ext n x
    rfl
  comul_counit := by
    ext n x
    rfl
  comul_assoc := by
    ext n x
    rfl

variable (k : Type u) [CommRing k]

noncomputable local instance universalCoverComonObjInstance :
    ComonObj (classifyingSpaceUniversalCover G) :=
  universalCoverComonObj G

noncomputable local instance linearizedUniversalCoverComonObjInstance :
    ComonObj
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G) :=
  Functor.obj.instComonObj _ (linearizationOnSimplicialObjects G k)

noncomputable local instance standardComplexComonObjInstance :
    ComonObj (Rep.standardComplex k G) :=
  Functor.obj.instComonObj _
    (AlgebraicTopology.alternatingFaceMapComplex (Rep k G))

noncomputable local instance barComplexComonObjInstance :
    ComonObj (Rep.barComplex k G) :=
  ComonObj.ofIso (Rep.barComplex.isoStandardComplex k G).symm

/-- Let `G` be a group, `k` a commutative ring, `S = Rep.standardComplex k G`, and `Δ =
standardComplexDiagonal G k`. Then `Δ ≫ (S ◁ Δ) = Δ ≫ (Δ ▷ S) ≫ (α_ S S S).hom` as chain maps
`S → S ⊗ (S ⊗ S)`, where tensor products and the associator are those of chain complexes of
representations. -/
theorem standardComplexDiagonal_assoc :
    standardComplexDiagonal G k ≫
        (Rep.standardComplex k G ◁ standardComplexDiagonal G k) =
      standardComplexDiagonal G k ≫
        (standardComplexDiagonal G k ▷ Rep.standardComplex k G) ≫
        (α_ (Rep.standardComplex k G)
          (Rep.standardComplex k G) (Rep.standardComplex k G)).hom :=
  ComonObj.comul_assoc (Rep.standardComplex k G)

/-- Let `G` be a group, `k` a commutative ring, `K = Rep.barComplex k G`, and `Δ =
barComplexDiagonal G k`. Then `Δ ≫ (K ◁ Δ) = Δ ≫ (Δ ▷ K) ≫ (α_ K K K).hom` as chain maps `K →
K ⊗ (K ⊗ K)`, with the chain-complex tensor product and associator. -/
theorem barComplexDiagonal_assoc :
    barComplexDiagonal G k ≫
        (Rep.barComplex k G ◁ barComplexDiagonal G k) =
      barComplexDiagonal G k ≫
        (barComplexDiagonal G k ▷ Rep.barComplex k G) ≫
        (α_ (Rep.barComplex k G)
          (Rep.barComplex k G) (Rep.barComplex k G)).hom :=
  ComonObj.comul_assoc (Rep.barComplex k G)

/-- Let `G` be a group, `k` a commutative ring, `A,B,D` representations, and `p,q,r : ℕ`. Put
`Y(A)_n = Hom_G((Rep.barComplex k G).X n,A)` and write `P` for the bar cup pairings. Then
`(P_{A,B}(p,q) ⊗ 𝟙) ≫ P_{A⊗B,D}(p+q,r) ≫ α_* ≫ e = α_{Y(A)_p,Y(B)_q,Y(D)_r} ≫ (𝟙 ⊗
P_{B,D}(q,r)) ≫ P_{A,B⊗D}(p,q+r)`. Here `α_*` postcomposes bar cochains by `(α_ A B D).hom`,
and `e` identifies `(p + q) + r` with `p + (q + r)`. -/
theorem barCochainCupPairing_assoc
    (A B D : Rep k G) (p q r : ℕ) :
    ((barCochainCupPairing G k A B).pair p q ⊗ₘ
        𝟙 (((Rep.barComplex k G).linearYonedaObj k D).X r)) ≫
      (barCochainCupPairing G k (A ⊗ B) D).pair (p + q) r ≫
      (HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
        (𝟙 (Rep.barComplex k G)) (α_ A B D).hom).f ((p + q) + r) ≫
      (((Rep.barComplex k G).linearYonedaObj k (A ⊗ (B ⊗ D))).XIsoOfEq
        (Nat.add_assoc p q r)).hom =
    (α_ (((Rep.barComplex k G).linearYonedaObj k A).X p)
      (((Rep.barComplex k G).linearYonedaObj k B).X q)
      (((Rep.barComplex k G).linearYonedaObj k D).X r)).hom ≫
      (𝟙 (((Rep.barComplex k G).linearYonedaObj k A).X p) ⊗ₘ
        (barCochainCupPairing G k B D).pair q r) ≫
      (barCochainCupPairing G k A (B ⊗ D)).pair p (q + r) := by
  apply HomologicalComplex.linearYonedaCochainPair_associativity_of_diagrams
  · rw [show HomologicalComplex.tensorHom (barComplexDiagonal G k)
        (𝟙 (Rep.barComplex k G)) =
          barComplexDiagonal G k ▷ Rep.barComplex k G by rfl]
    rw [show HomologicalComplex.tensorHom (𝟙 (Rep.barComplex k G))
        (barComplexDiagonal G k) =
          Rep.barComplex k G ◁ barComplexDiagonal G k by rfl]
    simpa only [Category.id_comp] using (barComplexDiagonal_assoc G k).symm
  · simp

/-- Let `G` be a group, `k` a commutative ring, `A,B,D` representations, and `p,q,r : ℕ`. For the
bar-cochain complexes `Y(A)_n = Hom_G((Rep.barComplex k G).X n,A)`, their homology cup maps
`P^H` satisfy `(P^H_{A,B}(p,q) ⊗ 𝟙) ≫ P^H_{A⊗B,D}(p+q,r) ≫ α_*^h = α_{H^pY(A),H^qY(B),H^rY(D)}
≫ (𝟙 ⊗ P^H_{B,D}(q,r)) ≫ P^H_{A,B⊗D}(p,q+r)`. The map `α_*^h` is induced by the coefficient
associator and the degree equality `h : (p + q) + r = p + (q + r)`. -/
theorem barCochainCupPairing_pairHomology_assoc
    (A B D : Rep k G) (p q r : ℕ) :
    ((barCochainCupPairing G k A B).pairHomology p q ⊗ₘ
        𝟙 (((Rep.barComplex k G).linearYonedaObj k D).homology r)) ≫
      (barCochainCupPairing G k (A ⊗ B) D).pairHomology (p + q) r ≫
      HomologicalComplex.cochainHomologyMapOfEq k
        (HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
          (𝟙 (Rep.barComplex k G)) (α_ A B D).hom)
        (Nat.add_assoc p q r) =
    (α_ (((Rep.barComplex k G).linearYonedaObj k A).homology p)
      (((Rep.barComplex k G).linearYonedaObj k B).homology q)
      (((Rep.barComplex k G).linearYonedaObj k D).homology r)).hom ≫
      (𝟙 (((Rep.barComplex k G).linearYonedaObj k A).homology p) ⊗ₘ
        (barCochainCupPairing G k B D).pairHomology q r) ≫
      (barCochainCupPairing G k A (B ⊗ D)).pairHomology p (q + r) := by
  let comparison :
      (Rep.barComplex k G).linearYonedaObj k ((A ⊗ B) ⊗ D) ⟶
        (Rep.barComplex k G).linearYonedaObj k (A ⊗ (B ⊗ D)) :=
    HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
      (𝟙 (Rep.barComplex k G)) (α_ A B D).hom
  apply HomologicalComplex.CochainGradedPairing.pairHomology_associativity_of_pair
    k (barCochainCupPairing G k A B)
    (barCochainCupPairing G k (A ⊗ B) D)
    (barCochainCupPairing G k B D)
    (barCochainCupPairing G k A (B ⊗ D))
    p q r
    (HomologicalComplex.cochainMapXOfEq k comparison (Nat.add_assoc p q r))
    (HomologicalComplex.cochainCyclesMapOfEq k comparison (Nat.add_assoc p q r))
    (HomologicalComplex.cochainHomologyMapOfEq k comparison (Nat.add_assoc p q r))
  · exact HomologicalComplex.cochainCyclesMapOfEq_i k comparison
      (Nat.add_assoc p q r)
  · exact HomologicalComplex.cochainHomologyπ_comp_cochainHomologyMapOfEq
      k comparison (Nat.add_assoc p q r)
  · dsimp [comparison, HomologicalComplex.cochainMapXOfEq]
    convert barCochainCupPairing_assoc G k A B D p q r using 1

section

set_option backward.isDefEq.respectTransparency false

/-- For a representation `A` of a group `G` over a commutative ring `k` and `n : ℕ`, the
isomorphism `H^n(G,A) ≅ H^n(Y(A))` is induced by `inhomogeneousCochainsIso A`, where `Y(A)_j =
Hom_G((Rep.barComplex k G).X j,A)` is the equivariant bar-cochain complex. -/
noncomputable def inhomogeneousBarHomologyIso
    (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅
      ((Rep.barComplex k G).linearYonedaObj k A).homology n :=
  HomologicalComplex.homologyMapIso (inhomogeneousCochainsIso A) n

/-- Let `G` be a group, `k` a commutative ring, `A,B` representations, and `p,q : ℕ`. Write
`I_n(A) = inhomogeneousBarHomologyIso G k A n` and `P^H` for the bar-cochain homology pairing.
Then `cup G k A B p q = (I_p(A).hom ⊗ I_q(B).hom) ≫ P^H_{A,B}(p,q) ≫ I_{p+q}(A ⊗ B).inv`, as
maps `H^p(G,A) ⊗ H^q(G,B) → H^{p+q}(G,A ⊗ B)`. -/
theorem cup_eq_barCochainCupPairing_transport
    (A B : Rep k G) (p q : ℕ) :
    cup G k A B p q =
      ((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
        (inhomogeneousBarHomologyIso G k B q).hom) ≫
        (barCochainCupPairing G k A B).pairHomology p q ≫
        (inhomogeneousBarHomologyIso G k (A ⊗ B) (p + q)).inv := by
  unfold cup inhomogeneousBarHomologyIso inhomogeneousCupPairing
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_whisker]
  rfl

/-- Let `k` be a commutative ring, `G` a group, `f : A → B` a morphism of representations, and `h
: n = n'` an equality of natural-number degrees. For `I_n(A) : H^n(G,A) ≅ H^n(Y(A))`, the
bar-homology comparison, `I_n(A).inv ≫ f_*^n ≫ E_B(h) = H(Y(f),h) ≫ I_{n'}(B).inv`. Here
`Y(f)` postcomposes equivariant bar cochains by `f`, `E_B(h)` identifies the two
group-cohomology degrees, and `H(Y(f),h)` induces the bar-homology map with target degree
`n'`. -/
theorem inhomogeneousBarHomologyIso_inv_naturality
    {A B : Rep k G} (f : A ⟶ B) {n n' : ℕ} (h : n = n') :
    (inhomogeneousBarHomologyIso G k A n).inv ≫
        map (MonoidHom.id G) f n ≫
        (HomologicalComplex.cochainHomologyIsoOfEq k
          (inhomogeneousCochains B) h).hom =
      HomologicalComplex.cochainHomologyMapOfEq k
        (HomologicalComplex.linearYonedaCochainComparison k (Rep k G)
          (𝟙 (Rep.barComplex k G)) f) h ≫
        (inhomogeneousBarHomologyIso G k B n').inv := by
  subst n'
  dsimp only [HomologicalComplex.cochainHomologyIsoOfEq,
    HomologicalComplex.cochainHomologyMapOfEq]
  erw [Category.comp_id]
  have hh := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (inhomogeneousCochainsIso_inv_naturality f)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hh
  simpa [inhomogeneousBarHomologyIso, map,
    HomologicalComplex.linearYonedaCochainComparison] using hh

/-- Let `G` be a group, `k` a commutative ring, `A,B,D` representations, and `p,q,r : ℕ`. Write
`C_{A,B}(p,q) = cup G k A B p q`. Then `(C_{A,B}(p,q) ⊗ 𝟙) ≫ C_{A⊗B,D}(p+q,r) ≫ (α_ A B D)_* ≫
e = α_{H^p(G,A),H^q(G,B),H^r(G,D)} ≫ (𝟙 ⊗ C_{B,D}(q,r)) ≫ C_{A,B⊗D}(p,q+r)`. The common target
is `H^{p+(q+r)}(G,A ⊗ (B ⊗ D))`, and `e` is induced by `(p + q) + r = p + (q + r)`. -/
theorem cup_assoc (A B D : Rep k G) (p q r : ℕ) :
    ((cup G k A B p q ⊗ₘ 𝟙 (groupCohomology D r)) ≫
        cup G k (A ⊗ B) D (p + q) r ≫
        map (MonoidHom.id G) (α_ A B D).hom ((p + q) + r) ≫
        (HomologicalComplex.cochainHomologyIsoOfEq k
          (inhomogeneousCochains (A ⊗ (B ⊗ D)))
          (Nat.add_assoc p q r)).hom) =
      (α_ (groupCohomology A p) (groupCohomology B q)
        (groupCohomology D r)).hom ≫
        (𝟙 (groupCohomology A p) ⊗ₘ cup G k B D q r) ≫
        cup G k A (B ⊗ D) p (q + r) := by
  rw [cup_eq_barCochainCupPairing_transport,
    cup_eq_barCochainCupPairing_transport,
    cup_eq_barCochainCupPairing_transport,
    cup_eq_barCochainCupPairing_transport]
  have hOut := inhomogeneousBarHomologyIso_inv_naturality G k
    (α_ A B D).hom (Nat.add_assoc p q r)
  simp only [Category.assoc]
  rw [hOut]
  have hLeft :
      ((((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k B q).hom) ≫
          (barCochainCupPairing G k A B).pairHomology p q ≫
          (inhomogeneousBarHomologyIso G k (A ⊗ B) (p + q)).inv) ⊗ₘ
        𝟙 (groupCohomology D r)) ≫
        ((inhomogeneousBarHomologyIso G k (A ⊗ B) (p + q)).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k D r).hom) =
      ((((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k B q).hom) ⊗ₘ
          (inhomogeneousBarHomologyIso G k D r).hom) ≫
        ((barCochainCupPairing G k A B).pairHomology p q ⊗ₘ
          𝟙 (((Rep.barComplex k G).linearYonedaObj k D).homology r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp [Category.assoc]
  rw [← Category.assoc, hLeft]
  have hRight :
      (α_ (groupCohomology A p) (groupCohomology B q)
          (groupCohomology D r)).hom ≫
        (𝟙 (groupCohomology A p) ⊗ₘ
          (((inhomogeneousBarHomologyIso G k B q).hom ⊗ₘ
              (inhomogeneousBarHomologyIso G k D r).hom) ≫
            (barCochainCupPairing G k B D).pairHomology q r ≫
            (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).inv)) ≫
        ((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).hom) =
      (((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
          (inhomogeneousBarHomologyIso G k B q).hom) ⊗ₘ
          (inhomogeneousBarHomologyIso G k D r).hom) ≫
        (α_ (((Rep.barComplex k G).linearYonedaObj k A).homology p)
          (((Rep.barComplex k G).linearYonedaObj k B).homology q)
          (((Rep.barComplex k G).linearYonedaObj k D).homology r)).hom ≫
        (𝟙 (((Rep.barComplex k G).linearYonedaObj k A).homology p) ⊗ₘ
          (barCochainCupPairing G k B D).pairHomology q r) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.assoc]
    have hBD :
        ((inhomogeneousBarHomologyIso G k B q).hom ⊗ₘ
            (inhomogeneousBarHomologyIso G k D r).hom) ≫
          (barCochainCupPairing G k B D).pairHomology q r ≫
          (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).inv ≫
          (inhomogeneousBarHomologyIso G k (B ⊗ D) (q + r)).hom =
        ((inhomogeneousBarHomologyIso G k B q).hom ⊗ₘ
            (inhomogeneousBarHomologyIso G k D r).hom) ≫
          (barCochainCupPairing G k B D).pairHomology q r := by
      simp
    rw [hBD]
    rw [← MonoidalCategory.tensorHom_comp_whiskerLeft]
    rw [← MonoidalCategory.associator_naturality_assoc]
    rw [MonoidalCategory.id_tensorHom]
  have hRightFull := congrArg (fun f =>
    f ≫ (barCochainCupPairing G k A (B ⊗ D)).pairHomology p (q + r) ≫
      (inhomogeneousBarHomologyIso G k (A ⊗ (B ⊗ D))
        (p + (q + r))).inv) hRight
  simp only [Category.assoc] at hRightFull
  rw [hRightFull]
  have hBar := barCochainCupPairing_pairHomology_assoc G k A B D p q r
  have hBarTransported := congrArg (fun f =>
    ((((inhomogeneousBarHomologyIso G k A p).hom ⊗ₘ
        (inhomogeneousBarHomologyIso G k B q).hom) ⊗ₘ
        (inhomogeneousBarHomologyIso G k D r).hom) ≫ f ≫
      (inhomogeneousBarHomologyIso G k (A ⊗ (B ⊗ D))
        (p + (q + r))).inv)) hBar
  simp only [Category.assoc] at hBarTransported
  convert hBarTransported using 1

/-- Let `G` be a group, `k` a commutative ring, and `A,B,D` representations. For `p,q,r : ℕ` and
classes `x ∈ H^p(G,A)`, `y ∈ H^q(G,B)`, `z ∈ H^r(G,D)`, `e((α_ A B D)_*((x ∪ y) ∪ z)) = x ∪ (y
∪ z)` in `H^{p+(q+r)}(G,A ⊗ (B ⊗ D))`. The map `e` is the canonical homology identification
for `(p + q) + r = p + (q + r)`. -/
theorem cup_assoc_tmul
    (A B D : Rep k G) (p q r : ℕ)
    (x : groupCohomology A p) (y : groupCohomology B q)
    (z : groupCohomology D r) :
    (HomologicalComplex.cochainHomologyIsoOfEq k
        (inhomogeneousCochains (A ⊗ (B ⊗ D)))
        (Nat.add_assoc p q r)).hom.hom
      ((map (MonoidHom.id G) (α_ A B D).hom ((p + q) + r)).hom
        ((cup G k (A ⊗ B) D (p + q) r).hom
          ((cup G k A B p q).hom (x ⊗ₜ[k] y) ⊗ₜ[k] z))) =
    (cup G k A (B ⊗ D) p (q + r)).hom
      (x ⊗ₜ[k] (cup G k B D q r).hom (y ⊗ₜ[k] z)) := by
  have h := congrArg (fun f => f.hom ((x ⊗ₜ[k] y) ⊗ₜ[k] z))
    (cup_assoc G k A B D p q r)
  change (HomologicalComplex.cochainHomologyIsoOfEq k
      (inhomogeneousCochains (A ⊗ (B ⊗ D)))
      (Nat.add_assoc p q r)).hom.hom
    ((map (MonoidHom.id G) (α_ A B D).hom ((p + q) + r)).hom
      ((cup G k (A ⊗ B) D (p + q) r).hom
        ((cup G k A B p q).hom (x ⊗ₜ[k] y) ⊗ₜ[k] z))) =
      (cup G k A (B ⊗ D) p (q + r)).hom
        (x ⊗ₜ[k] (cup G k B D q r).hom (y ⊗ₜ[k] z)) at h
  exact h

end

end groupCohomology
