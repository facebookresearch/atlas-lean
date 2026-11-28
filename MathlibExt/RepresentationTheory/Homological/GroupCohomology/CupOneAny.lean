/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.Homology

/-!
# Cup products with a degree-one left factor

Let `G` be a group, `k` a commutative ring, and `A,B` representations. The cup product with
left degree one is regarded as a map `H¹(G,A) ⊗ H^q(G,B) → H^{q+1}(G,A ⊗ B)` by the canonical
homology isomorphism for `1 + q = q + 1`.

A fixed class `x ∈ H¹(G,A)` and an equivariant pairing `μ : A ⊗ B → C` give the linear
operator `y ↦ μ_*(x ∪ y)` from `H^q(G,B)` to `H^{q+1}(G,C)`. These products commute with group
pullback and compatible coefficient maps. Their values on cycle representatives use the same
canonical degree identification.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- For representations `A,B` of a group `G` over a commutative ring `k` and `q : ℕ`, the morphism
`H¹(G,A) ⊗ₖ H^q(G,B) → H^{q+1}(G,A ⊗ B)` is `cup G k A B 1 q` followed by the homology
isomorphism of the inhomogeneous cochain complex induced by `1 + q = q + 1`. -/
noncomputable def cupOneAny
    (A B : Rep k G) (q : ℕ) :
    groupCohomology A 1 ⊗ groupCohomology B q ⟶
      groupCohomology (A ⊗ B) (q + 1) :=
  cup G k A B 1 q ≫
    ((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
      (Nat.one_add q)).hom

/-- Let `A,B,C` be representations of a group `G` over a commutative ring `k`, `x ∈ H¹(G,A)`, and
`μ : A ⊗ B → C` an equivariant morphism. For `q : ℕ`, `cupOneClassMap x μ q : H^q(G,B) →
H^{q+1}(G,C)` sends `y` to `μ_*((cupOneAny A B q)(x ⊗ₜ[k] y))`. -/
noncomputable def cupOneClassMap
    {A B C : Rep k G} (x : groupCohomology A 1)
    (mu : A ⊗ B ⟶ C) (q : ℕ) :
    groupCohomology B q ⟶ groupCohomology C (q + 1) :=
  ModuleCat.ofHom
      ((TensorProduct.mk k
        (groupCohomology A 1) (groupCohomology B q)) x) ≫
    cupOneAny A B q ≫
    map (MonoidHom.id G) mu (q + 1)

@[simp]
theorem cupOneClassMap_apply
    {A B C : Rep k G} (x : groupCohomology A 1)
    (mu : A ⊗ B ⟶ C) (q : ℕ) (y : groupCohomology B q) :
    (cupOneClassMap x mu q).hom y =
      (map (MonoidHom.id G) mu (q + 1)).hom
        ((cupOneAny A B q).hom (x ⊗ₜ[k] y)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let `k` be a commutative ring, `f : J →* G` a group homomorphism, `A,B : Rep k G`, and `A',B'
: Rep k J`. Given `φ : Rep.res f A → A'` and `ψ : Rep.res f B → B'`, set `θ =
(Rep.resTensorIso f A B).inv ≫ (φ ⊗ ψ)`. For every `q : ℕ`, `cupOneAny A B q ≫ map f θ (q + 1)
= (map f φ 1 ⊗ map f ψ q) ≫ cupOneAny A' B' q`. -/
theorem cupOneAny_naturality_of_hom
    {J : Type u} [Group J]
    {A B : Rep k G} {A' B' : Rep k J}
    (f : J →* G) (phi : Rep.res f A ⟶ A')
    (psi : Rep.res f B ⟶ B') (q : ℕ) :
    cupOneAny A B q ≫
        map f ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)) (q + 1) =
      (map f phi 1 ⊗ₘ map f psi q) ≫ cupOneAny A' B' q := by
  let coeff := (Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)
  have hcast := HomologicalComplex.homologyIsoOfEq_hom_naturality
    (cochainsMap f coeff) (Nat.one_add q)
  unfold cupOneAny
  rw [Category.assoc]
  rw [← hcast]
  rw [← Category.assoc]
  rw [cup_naturality_of_hom f phi psi 1 q]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, and `φ : A → A'`, `ψ : B → B'` morphisms of
representations. For every `q : ℕ`, `cupOneAny A B q ≫ map (id G) (φ ⊗ ψ) (q + 1) = (map (id
G) φ 1 ⊗ map (id G) ψ q) ≫ cupOneAny A' B' q`, as maps from `H¹(G,A) ⊗ H^q(G,B)` to
`H^{q+1}(G,A' ⊗ B')`. -/
theorem cupOneAny_naturality
    {A B A' B' : Rep k G} (phi : A ⟶ A') (psi : B ⟶ B')
    (q : ℕ) :
    cupOneAny A B q ≫
        map (MonoidHom.id G) (phi ⊗ₘ psi) (q + 1) =
      (map (MonoidHom.id G) phi 1 ⊗ₘ
        map (MonoidHom.id G) psi q) ≫ cupOneAny A' B' q := by
  let coeff := (Rep.resTensorIso (MonoidHom.id G) A B).inv ≫
    (phi ⊗ₘ psi)
  have hmap : map (MonoidHom.id G) coeff (q + 1) =
      map (MonoidHom.id G) (phi ⊗ₘ psi) (q + 1) := by
    apply map_congr rfl
    rfl
  rw [← hmap]
  exact cupOneAny_naturality_of_hom
    (f := MonoidHom.id G) phi psi q

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `k` be a commutative ring and `G` a group. For representations `A,B,C,A',B',C'`, pairings
`μ : A ⊗ B → C`, `μ' : A' ⊗ B' → C'`, and morphisms `φ : A → A'`, `ψ : B → B'`, `ω : C → C'`,
assume `(φ ⊗ ψ) ≫ μ' = μ ≫ ω`. For `x ∈ H¹(G,A)` and `q : ℕ`, `cupOneClassMap x μ q ≫ ω_* =
ψ_* ≫ cupOneClassMap (φ_*x) μ' q`, where the induced maps have degrees `q + 1`, `q`, and `1`,
respectively. -/
theorem cupOneClassMap_naturality
    {A B C A' B' C' : Rep k G}
    (x : groupCohomology A 1)
    (mu : A ⊗ B ⟶ C) (mu' : A' ⊗ B' ⟶ C')
    (phi : A ⟶ A') (psi : B ⟶ B') (omega : C ⟶ C')
    (hmu : (phi ⊗ₘ psi) ≫ mu' = mu ≫ omega)
    (q : ℕ) :
    cupOneClassMap x mu q ≫
        map (MonoidHom.id G) omega (q + 1) =
      map (MonoidHom.id G) psi q ≫
        cupOneClassMap
          ((map (MonoidHom.id G) phi 1).hom x) mu' q := by
  let i := ModuleCat.ofHom
    ((TensorProduct.mk k
      (groupCohomology A 1) (groupCohomology B q)) x)
  let i' := ModuleCat.ofHom
    ((TensorProduct.mk k
      (groupCohomology A' 1) (groupCohomology B' q))
        ((map (MonoidHom.id G) phi 1).hom x))
  let hphi := map (MonoidHom.id G) phi 1
  let hpsi := map (MonoidHom.id G) psi q
  have hi : i ≫ (hphi ⊗ₘ hpsi) = hpsi ≫ i' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  change (i ≫ cupOneAny A B q ≫ map (MonoidHom.id G) mu (q + 1)) ≫
      map (MonoidHom.id G) omega (q + 1) =
    hpsi ≫
      (i' ≫ cupOneAny A' B' q ≫
        map (MonoidHom.id G) mu' (q + 1))
  calc
    (i ≫ cupOneAny A B q ≫ map (MonoidHom.id G) mu (q + 1)) ≫
          map (MonoidHom.id G) omega (q + 1) =
      i ≫ cupOneAny A B q ≫
        map (MonoidHom.id G) (mu ≫ omega) (q + 1) := by
          rw [Category.assoc, Category.assoc, ← map_id_comp]
    _ = i ≫ cupOneAny A B q ≫
        map (MonoidHom.id G) ((phi ⊗ₘ psi) ≫ mu') (q + 1) := by
          rw [hmu]
    _ = i ≫ cupOneAny A B q ≫
        (map (MonoidHom.id G) (phi ⊗ₘ psi) (q + 1) ≫
          map (MonoidHom.id G) mu' (q + 1)) := by
            rw [map_id_comp]
    _ = i ≫
        ((map (MonoidHom.id G) phi 1 ⊗ₘ
          map (MonoidHom.id G) psi q) ≫ cupOneAny A' B' q) ≫
        map (MonoidHom.id G) mu' (q + 1) := by
          rw [← cupOneAny_naturality phi psi q]
          simp only [Category.assoc]
    _ = (i ≫ (hphi ⊗ₘ hpsi)) ≫ cupOneAny A' B' q ≫
        map (MonoidHom.id G) mu' (q + 1) := by
          rfl
    _ = (hpsi ≫ i') ≫ cupOneAny A' B' q ≫
        map (MonoidHom.id G) mu' (q + 1) := by rw [hi]
    _ = hpsi ≫
        (i' ≫ cupOneAny A' B' q ≫
          map (MonoidHom.id G) mu' (q + 1)) := by
            simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `k` be a commutative ring, `G` a group, `U = 𝟙_ (Rep k G)` the tensor-unit representation,
`x ∈ H¹(G,U)`, `B,A' : Rep k G`, and `φ : U → A'`. For `q : ℕ`, cupping with `x` via the left
unitor `λ_B : U ⊗ B → B`, then mapping by `λ_B.inv ≫ (φ ⊗ 𝟙 B) : B → A' ⊗ B`, equals
`cupOneClassMap (φ_*x) (𝟙 (A' ⊗ B)) q`. -/
theorem cupOneClassMap_leftUnitor_naturality
    {A' B : Rep k G}
    (x : groupCohomology (𝟙_ (Rep k G)) 1)
    (phi : 𝟙_ (Rep k G) ⟶ A') (q : ℕ) :
    cupOneClassMap x (λ_ B).hom q ≫
        map (MonoidHom.id G)
          ((λ_ B).inv ≫ (phi ⊗ₘ 𝟙 B)) (q + 1) =
      cupOneClassMap
        ((map (MonoidHom.id G) phi 1).hom x)
        (𝟙 (A' ⊗ B)) q := by
  have hmu : (phi ⊗ₘ 𝟙 B) ≫ 𝟙 (A' ⊗ B) =
      (λ_ B).hom ≫ ((λ_ B).inv ≫ (phi ⊗ₘ 𝟙 B)) := by
    simp
  have h := cupOneClassMap_naturality
    x (λ_ B).hom (𝟙 (A' ⊗ B)) phi (𝟙 B)
      ((λ_ B).inv ≫ (phi ⊗ₘ 𝟙 B)) hmu q
  rw [map_id, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- For representations `A,B` of a group `G` over a commutative ring `k`, `cupOneAny A B 1 = cup G
k A B 1 1` as morphisms `H¹(G,A) ⊗ H¹(G,B) → H²(G,A ⊗ B)`. The canonical degree identification
for `1 + 1 = 1 + 1` is the identity. -/
theorem cupOneAny_one_eq (A B : Rep k G) :
    cupOneAny A B 1 = cup G k A B 1 1 := by
  unfold cupOneAny
  rw [show Nat.one_add 1 = (rfl : 1 + 1 = 1 + 1) from
    Subsingleton.elim _ _]
  change cup G k A B 1 1 ≫ 𝟙 _ = _
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, `q : ℕ`, and `x,y`
cycles of the inhomogeneous cochain complexes in degrees `1,q`, respectively. Then `cupOneAny
A B q (π A 1 x ⊗ₜ[k] π B q y) = π (A ⊗ B) (q + 1) (e_Z ((inhomogeneousCupPairing G k A
B).pairCycles 1 q (x ⊗ₜ[k] y)))`, where `e_Z` is the cycles isomorphism induced by `1 + q = q
+ 1`. -/
theorem cupOneAny_π_apply
    (A B : Rep k G) (q : ℕ)
    (x : cocycles A 1) (y : cocycles B q) :
    cupOneAny A B q
        (π A 1 x ⊗ₜ[k] π B q y) =
      π (A ⊗ B) (q + 1)
        (((inhomogeneousCochains (A ⊗ B)).cyclesIsoOfEq
          (Nat.one_add q)).hom.hom
          (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
            (x ⊗ₜ[k] y))) := by
  rw [cupOneAny]
  change (((cup G k A B 1 q ≫
      ((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
        (Nat.one_add q)).hom).hom)
      (π A 1 x ⊗ₜ[k] π B q y) = _)
  unfold cup
  change (((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
      (Nat.one_add q)).hom.hom
        (((inhomogeneousCupPairing G k A B).pairHomology 1 q).hom
          (((inhomogeneousCochains A).homologyπ 1).hom x ⊗ₜ[k]
            ((inhomogeneousCochains B).homologyπ q).hom y))) = _
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply]
  have h := ConcreteCategory.congr_hom
    ((inhomogeneousCochains (A ⊗ B)
      ).homologyπ_comp_homologyIsoOfEq_hom (Nat.one_add q))
    (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
      (x ⊗ₜ[k] y))
  change _ = ((inhomogeneousCochains (A ⊗ B)).homologyπ (q + 1)).hom
    (((inhomogeneousCochains (A ⊗ B)).cyclesIsoOfEq
      (Nat.one_add q)).hom.hom
      (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
        (x ⊗ₜ[k] y)))
  simpa only [ConcreteCategory.comp_apply] using h

end groupCohomology
