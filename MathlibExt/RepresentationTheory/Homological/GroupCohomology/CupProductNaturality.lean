/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProduct
public import MathlibExt.RepresentationTheory.Rep.ResTensor

/-!
# Naturality of group-cohomology cup products

Let `G` be a group and `k` a commutative ring. The comparison between inhomogeneous cochains
and equivariant bar cochains commutes with postcomposition by coefficient morphisms. For `f :
A → A'` and `g : B → B'`, both cochain cup pairings and the cohomology product satisfy `(f ⊗
g)_*(x ∪ y) = f_*x ∪ g_*y` in all degrees `p,q : ℕ`.

For a group homomorphism `f : G →* H`, coefficient maps `φ : Rep.res f A → A'` and `ψ :
Rep.res f B → B'` give the same identities after pullback. The output coefficient map is
`(Rep.resTensorIso f A B).inv ≫ (φ ⊗ ψ)`, from `Rep.res f (A ⊗ B)` to `A' ⊗ B'`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite
open HomologicalComplex

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

@[simp]
private lemma moduleHom_comp_apply {A B C : ModuleCat k}
    (a : A ⟶ B) (b : B ⟶ C) (x : A) :
    (a ≫ b).hom x = b.hom (a.hom x) :=
  rfl

private lemma cochainsMap_id_apply
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (phi : (Fin n → G) → A) (x : Fin n → G) :
    ((cochainsMap (MonoidHom.id G) f).f n).hom phi x = f.hom (phi x) :=
  rfl

private lemma cochainsMap_restricted_apply
    {G H : Type u} [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ B) (n : ℕ)
    (a : (Fin n → H) → A) (g : Fin n → G) :
    ((cochainsMap f phi).f n).hom a g = phi.hom (a (fun i => f (g i))) :=
  rfl

private lemma coefficientTensorMap_tmul {A B C D : ModuleCat k}
    (f : A ⟶ B) (g : C ⟶ D) (a : A) (b : C) :
    (f ⊗ₘ g).hom (a ⊗ₜ[k] b) = f.hom a ⊗ₜ[k] g.hom b :=
  rfl

private lemma coefficientMap_apply_basis
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (phi : Rep.free k G (Fin n → G) ⟶ A) (x : Fin n → G) :
    (((((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
      (op (Rep.barComplex k G))).f n).hom phi).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      f.hom (phi.hom (Finsupp.single x (MonoidAlgebra.single 1 1))) :=
  rfl

/-- Let `k` be a commutative ring, `G` a group, and `f : A → B` a morphism of representations.
Write `I_A : C^*(G,A) ≅ Y(A)` for `inhomogeneousCochainsIso A`, where `Y(A)_n =
Hom_G((Rep.barComplex k G).X n,A)`, and let `Y(f)` be postcomposition by `f`. Then
`cochainsMap (id G) f ≫ I_B.hom = I_A.hom ≫ Y(f)` as cochain maps `C^*(G,A) → Y(B)`. -/
theorem inhomogeneousCochainsIso_hom_naturality
    {A B : Rep k G} (f : A ⟶ B) :
    cochainsMap (MonoidHom.id G) f ≫ (inhomogeneousCochainsIso B).hom =
      (inhomogeneousCochainsIso A).hom ≫
        (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
          (op (Rep.barComplex k G))) := by
  set_option backward.isDefEq.respectTransparency false in
  ext n phi
  apply Rep.free_ext
  intro x
  simp only [HomologicalComplex.comp_f]
  rw [moduleHom_comp_apply, moduleHom_comp_apply]
  have hIsoB :
      (((inhomogeneousCochainsIso B).hom.f n).hom
        (((cochainsMap (MonoidHom.id G) f).f n).hom phi)).hom
          (Finsupp.single x (MonoidAlgebra.single 1 1)) =
        ((cochainsMap (MonoidHom.id G) f).f n).hom phi x := by
    simpa using inhomogeneousCochainsIso_hom_apply_single_single G k B n
      (((cochainsMap (MonoidHom.id G) f).f n).hom phi) x 1 1
  rw [hIsoB, cochainsMap_id_apply]
  let phiBar : Rep.free k G (Fin n → G) ⟶ A :=
    ((inhomogeneousCochainsIso A).hom.f n).hom phi
  have hIso : phiBar.hom
      (Finsupp.single x (MonoidAlgebra.single 1 1)) = phi x := by
    simpa using (inhomogeneousCochainsIso_hom_apply_single_single
      G k A n phi x 1 1)
  have hCoeff := coefficientMap_apply_basis f n phiBar x
  exact (congrArg f.hom hIso.symm).trans hCoeff.symm

/-- Let `k` be a commutative ring, `G` a group, and `f : A → B` a morphism of representations. For
`I_A : C^*(G,A) ≅ Y(A)` and `I_B : C^*(G,B) ≅ Y(B)`, the inhomogeneous/bar comparisons, let
`Y(f)` postcompose each equivariant bar cochain with `f`. Then `I_A.inv ≫ cochainsMap (id G) f
= Y(f) ≫ I_B.inv` as maps `Y(A) → C^*(G,B)`. -/
theorem inhomogeneousCochainsIso_inv_naturality
    {A B : Rep k G} (f : A ⟶ B) :
    (inhomogeneousCochainsIso A).inv ≫
        cochainsMap (MonoidHom.id G) f =
      (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
          (op (Rep.barComplex k G))) ≫
        (inhomogeneousCochainsIso B).inv := by
  set_option backward.isDefEq.respectTransparency false in
  rw [← cancel_mono (inhomogeneousCochainsIso B).hom]
  simp only [Category.assoc]
  rw [inhomogeneousCochainsIso_hom_naturality f]
  simp

/-- Let `k` be a commutative ring, `G` a group, and `f : A → A'`, `g : B → B'` morphisms of
representations. Write `P_{A,B}` for the graded bar cup pairing and `Y_n(f)` for
postcomposition by `f` on degree-`n` equivariant bar cochains. For `p,q : ℕ`, `P_{A,B}(p,q) ≫
Y_{p+q}(f ⊗ g) = (Y_p(f) ⊗ Y_q(g)) ≫ P_{A',B'}(p,q)`. -/
theorem barCochainCupPairing_naturality
    {A B A' B' : Rep k G} (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) :
    (barCochainCupPairing G k A B).pair p q ≫
        (((linearHomCochainComplexBifunctor k (Rep k G)).map (f ⊗ₘ g)).app
          (op (Rep.barComplex k G))).f (p + q) =
      (((((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
          (op (Rep.barComplex k G))).f p) ⊗ₘ
        ((((linearHomCochainComplexBifunctor k (Rep k G)).map g).app
          (op (Rep.barComplex k G))).f q)) ≫
        (barCochainCupPairing G k A' B').pair p q := by
  apply linearYonedaCochainGradedPairing_coefficient_naturality
  simp

/-- Let `k` be a commutative ring, `G` a group, and `f : A → A'`, `g : B → B'` morphisms of
representations. Write `P_{A,B}` for `inhomogeneousCupPairing G k A B` and `c_n(f) =
(cochainsMap (id G) f).f n`. For `p,q : ℕ`, `P_{A,B}.pair p q ≫ c_{p+q}(f ⊗ g) = (c_p(f) ⊗
c_q(g)) ≫ P_{A',B'}.pair p q`. -/
theorem inhomogeneousCupPairing_naturality
    {A B A' B' : Rep k G} (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) :
    (inhomogeneousCupPairing G k A B).pair p q ≫
        (cochainsMap (MonoidHom.id G) (f ⊗ₘ g)).f (p + q) =
      ((cochainsMap (MonoidHom.id G) f).f p ⊗ₘ
        (cochainsMap (MonoidHom.id G) g).f q) ≫
        (inhomogeneousCupPairing G k A' B').pair p q := by
  set_option backward.isDefEq.respectTransparency false in
  rw [inhomogeneousCupPairing, inhomogeneousCupPairing]
  simp only [HomologicalComplex.CochainGradedPairing.whisker_pair]
  have hout :
      (inhomogeneousCochainsIso (A ⊗ B)).inv.f (p + q) ≫
          (cochainsMap (MonoidHom.id G) (f ⊗ₘ g)).f (p + q) =
        ((((linearHomCochainComplexBifunctor k (Rep k G)).map
          (f ⊗ₘ g)).app (op (Rep.barComplex k G))).f (p + q)) ≫
          (inhomogeneousCochainsIso (A' ⊗ B')).inv.f (p + q) := by
    simpa only [HomologicalComplex.comp_f] using congrArg
      (fun h => h.f (p + q))
      (inhomogeneousCochainsIso_inv_naturality (f ⊗ₘ g))
  have hA :
      (cochainsMap (MonoidHom.id G) f).f p ≫
          (inhomogeneousCochainsIso A').hom.f p =
        (inhomogeneousCochainsIso A).hom.f p ≫
          (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
            (op (Rep.barComplex k G))).f p := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun h => h.f p)
      (inhomogeneousCochainsIso_hom_naturality f)
  have hB :
      (cochainsMap (MonoidHom.id G) g).f q ≫
          (inhomogeneousCochainsIso B').hom.f q =
        (inhomogeneousCochainsIso B).hom.f q ≫
          (((linearHomCochainComplexBifunctor k (Rep k G)).map g).app
            (op (Rep.barComplex k G))).f q := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun h => h.f q)
      (inhomogeneousCochainsIso_hom_naturality g)
  simp only [Category.assoc]
  rw [hout]
  rw [← Category.assoc ((barCochainCupPairing G k A B).pair p q)]
  rw [barCochainCupPairing_naturality f g p q]
  let barF := (((linearHomCochainComplexBifunctor k (Rep k G)).map f).app
    (op (Rep.barComplex k G))).f p
  let barG := (((linearHomCochainComplexBifunctor k (Rep k G)).map g).app
    (op (Rep.barComplex k G))).f q
  let coF := (cochainsMap (MonoidHom.id G) f).f p
  let coG := (cochainsMap (MonoidHom.id G) g).f q
  let isoA := (inhomogeneousCochainsIso A).hom.f p
  let isoB := (inhomogeneousCochainsIso B).hom.f q
  let isoA' := (inhomogeneousCochainsIso A').hom.f p
  let isoB' := (inhomogeneousCochainsIso B').hom.f q
  have hTensorNat :
      (isoA ⊗ₘ isoB) ≫ (barF ⊗ₘ barG) =
        (coF ⊗ₘ coG) ≫ (isoA' ⊗ₘ isoB') := by
    dsimp only [barF, barG, coF, coG, isoA, isoB, isoA', isoB']
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, hA, hB]
  simpa only [Category.assoc] using congrArg
    (fun h => h ≫ (barCochainCupPairing G k A' B').pair p q ≫
      (inhomogeneousCochainsIso (A' ⊗ B')).inv.f (p + q)) hTensorNat

/-- Let `k` be a commutative ring, `G` a group, and `f : A → A'`, `g : B → B'` morphisms of
representations. For `p,q : ℕ`, `cup G k A B p q ≫ map (id G) (f ⊗ g) (p + q) = (map (id G) f
p ⊗ map (id G) g q) ≫ cup G k A' B' p q`, as maps into `H^{p+q}(G,A' ⊗ B')`. -/
theorem cup_naturality
    {A B A' B' : Rep k G} (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) :
    cup G k A B p q ≫
        map (MonoidHom.id G) (f ⊗ₘ g) (p + q) =
      (map (MonoidHom.id G) f p ⊗ₘ
        map (MonoidHom.id G) g q) ≫ cup G k A' B' p q := by
  symm
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality
    (inhomogeneousCupPairing G k A B)
    (inhomogeneousCupPairing G k A' B')
    (cochainsMap (MonoidHom.id G) f)
    (cochainsMap (MonoidHom.id G) g)
    (cochainsMap (MonoidHom.id G) (f ⊗ₘ g))
  intro i j
  exact inhomogeneousCupPairing_naturality f g i j

/-- Let `G,H` be groups, `f : G →* H`, `n : ℕ`, `x : Fin n → G`, and `i : Fin (n + 1)`. Then `f
(Fin.partialProd x i) = Fin.partialProd (fun j => f (x j)) i`. Thus applying `f` to the
ordered product of the first `i` entries equals the ordered product of their images, including
the empty product at `i = 0`. -/
theorem map_partialProd {G H : Type u} [Group G] [Group H]
    (f : G →* H) {n : ℕ} (x : Fin n → G) (i : Fin (n + 1)) :
    f (Fin.partialProd x i) =
      Fin.partialProd (fun j => f (x j)) i := by
  simp [Fin.partialProd, List.ofFn_comp', map_list_prod]

set_option backward.isDefEq.respectTransparency false in
/-- Let `k` be a commutative ring, `f : G →* H` a group homomorphism, `A,B : Rep k H`, and `A',B'
: Rep k G`. For `φ : Rep.res f A → A'`, `ψ : Rep.res f B → B'`, put `θ = (Rep.resTensorIso f A
B).inv ≫ (φ ⊗ ψ)` and `c_n(f,φ) = (cochainsMap f φ).f n`. For `p,q : ℕ`, the cup pairings
satisfy `P_H(A,B).pair p q ≫ c_{p+q}(f,θ) = (c_p(f,φ) ⊗ c_q(f,ψ)) ≫ P_G(A',B').pair p q`. -/
theorem inhomogeneousCupPairing_naturality_of_hom
    {G H : Type u} [Group G] [Group H]
    {A B : Rep k H} {A' B' : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (p q : ℕ) :
    (inhomogeneousCupPairing H k A B).pair p q ≫
        (cochainsMap f
          ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi))).f (p + q) =
      ((cochainsMap f phi).f p ⊗ₘ (cochainsMap f psi).f q) ≫
        (inhomogeneousCupPairing G k A' B').pair p q := by
  have hcoef (a : A) (b : B) :
      ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)).hom (a ⊗ₜ[k] b) =
        phi.hom a ⊗ₜ[k] psi.hom b := by
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      apply inhomogeneousCochains.ext
      intro g
      rw [moduleHom_comp_apply, moduleHom_comp_apply,
        coefficientTensorMap_tmul, cochainsMap_restricted_apply]
      rw [inhomogeneousCupPairing_apply, inhomogeneousCupPairing_apply]
      rw [hcoef]
      congr 1
      rw [← map_partialProd]
      have hy := cochainsMap_restricted_apply f psi q y
        (fun i => g (Fin.natAdd p i))
      exact (Rep.hom_comm_apply psi
        (Fin.partialProd g (Fin.natAdd p (0 : Fin (q + 1))))
        (y (fun i => f (g (Fin.natAdd p i))))).trans
          (congrArg (B'.ρ (Fin.partialProd g (Fin.natAdd p (0 : Fin (q + 1))))) hy.symm)
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Let `k` be a commutative ring, `f : G →* H` a group homomorphism, `A,B : Rep k H`, and `A',B'
: Rep k G`. Given `φ : Rep.res f A → A'` and `ψ : Rep.res f B → B'`, set `θ =
(Rep.resTensorIso f A B).inv ≫ (φ ⊗ ψ)`. For `p,q : ℕ`, `cup H k A B p q ≫ map f θ (p + q) =
(map f φ p ⊗ map f ψ q) ≫ cup G k A' B' p q`. -/
theorem cup_naturality_of_hom
    {G H : Type u} [Group G] [Group H]
    {A B : Rep k H} {A' B' : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (p q : ℕ) :
    cup H k A B p q ≫
        map f ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)) (p + q) =
      (map f phi p ⊗ₘ map f psi q) ≫ cup G k A' B' p q := by
  symm
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality
    (inhomogeneousCupPairing H k A B)
    (inhomogeneousCupPairing G k A' B')
    (cochainsMap f phi)
    (cochainsMap f psi)
    (cochainsMap f ((Rep.resTensorIso f A B).inv ≫ (phi ⊗ₘ psi)))
  intro i j
  exact inhomogeneousCupPairing_naturality_of_hom f phi psi i j

end groupCohomology
