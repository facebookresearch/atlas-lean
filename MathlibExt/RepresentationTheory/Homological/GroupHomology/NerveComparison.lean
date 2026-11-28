/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Monad.ClassifyingNerveData
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexFreeModule
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Lean.Elab.Tactic.Omega

/-!
# Group homology and the one-object nerve with trivial coefficients

Let k be a commutative ring and G a group in universe u.
The inhomogeneous chains with trivial coefficients k are canonically
isomorphic to the k-chain complex of B(Gᵐᵒᵖ), using the ordered-tuple
coordinate equivalence on one-object nerve simplices.

Inversion Gᵐᵒᵖ→G gives the direct-nerve comparison with BG.
Its generator convention sends (g₀,…,g_(n-1)) to the nerve simplex
with coordinates (g₀⁻¹,…,g_(n-1)⁻¹).
The comparisons preserve the chain differential and give
H_n(G,k_triv)≅H_n(BG;k), naturally under group homomorphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace groupHomology

private def pointIndex : Discrete PUnit.{1} := ⟨PUnit.unit⟩

section Coordinates

variable (G : Type u) [Monoid G]

private theorem oppositeNerveFaceReader (n : ℕ) (i : Fin (n + 2))
    (g : Fin (n + 1) → G) :
    CategoryTheory.nerve.singleObjOppEquiv G n
        ((CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).δ i
          ((CategoryTheory.nerve.singleObjOppEquiv G (n + 1)).symm g)) =
      CategoryTheory.Monad.barTupleEquiv G pointIndex n
        ((CategoryTheory.Monad.barEvalData G pointIndex).δ i
          ((CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1)).symm g)) := by
  let t := (CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1)).symm g
  have h := ConcreteCategory.congr_hom
    (CategoryTheory.Monad.tupleIso_face G pointIndex i) t
  change
    (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).δ i
        ((CategoryTheory.nerve.singleObjOppEquiv G (n + 1)).symm
          (CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1) t)) =
      (CategoryTheory.nerve.singleObjOppEquiv G n).symm
        (CategoryTheory.Monad.barTupleEquiv G pointIndex n
          ((CategoryTheory.Monad.barEvalData G pointIndex).δ i t)) at h
  have ht : CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1) t = g :=
    Equiv.apply_symm_apply _ _
  rw [ht] at h
  exact (congrArg (CategoryTheory.nerve.singleObjOppEquiv G n) h).trans
    (Equiv.apply_symm_apply _ _)

private theorem oppositeNerveFace_zero (n : ℕ) (g : Fin (n + 1) → G) :
    (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).δ (0 : Fin (n + 2))
        ((CategoryTheory.nerve.singleObjOppEquiv G (n + 1)).symm g) =
      (CategoryTheory.nerve.singleObjOppEquiv G n).symm (Fin.tail g) := by
  apply (CategoryTheory.nerve.singleObjOppEquiv G n).injective
  rw [oppositeNerveFaceReader, Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using
    CategoryTheory.Monad.barTuple_zero_face G pointIndex n
      ((CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1)).symm g)

private theorem oppositeNerveFace_succ (n : ℕ) (j : Fin (n + 1))
    (g : Fin (n + 1) → G) :
    (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).δ j.succ
        ((CategoryTheory.nerve.singleObjOppEquiv G (n + 1)).symm g) =
      (CategoryTheory.nerve.singleObjOppEquiv G n).symm
        (Fin.contractNth j (· * ·) g) := by
  apply (CategoryTheory.nerve.singleObjOppEquiv G n).injective
  rw [oppositeNerveFaceReader, Equiv.apply_symm_apply]
  let t := (CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1)).symm g
  have ht : CategoryTheory.Monad.barTupleEquiv G pointIndex (n + 1) t = g :=
    Equiv.apply_symm_apply _ _
  by_cases hlast : j.val = n
  · rw [CategoryTheory.Monad.barTuple_last_face G pointIndex n t j.succ
      (by change j.val + 1 = n + 1; omega), ht]
    funext r
    have hr : r.val < j.val := by omega
    exact (Fin.contractNth_apply_of_lt j (· * ·) g r hr).symm
  · have hj : j.val < n := by omega
    let k : Fin n := ⟨j.val, hj⟩
    rw [CategoryTheory.Monad.barTuple_middle_face G pointIndex n t k j.succ rfl, ht]
    have hk : k.castSucc = j := Fin.ext rfl
    simp only [CategoryTheory.Monad.tupleMulAt, hk]

end Coordinates

section Chains

variable (k G : Type u) [CommRing k] [Group G]

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The degree n isomorphism from inhomogeneous trivial-coefficient
chains to k-chains on B(Gᵐᵒᵖ) identifies a basis tuple g with the
simplex (e_n^op)⁻¹(g). -/
def trivialOppositeNerveChainObjIso (n : ℕ) :
    (inhomogeneousChains (Rep.trivial k G k)).X n ≅
      ((CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).chainComplex
        (ModuleCat.of k k : ModuleCat.{u} k)).X n :=
  (Finsupp.domLCongr (CategoryTheory.nerve.singleObjOppEquiv G n).symm :
    ((Fin n → G) →₀ k) ≃ₗ[k] ((CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)) _⦋n⦌ →₀ k)).toModuleIso ≪≫
    (SSet.chainComplexFreeIso (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)) k n).symm

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The basis inclusion at g∈G^n followed by the opposite-nerve
comparison is the simplex-chain inclusion at (e_n^op)⁻¹(g). -/
theorem trivialOppositeNerveChainObjIso_generator (n : ℕ) (g : Fin n → G) :
    ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) ≫
        (trivialOppositeNerveChainObjIso k G n).hom =
      (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k))
        ((CategoryTheory.nerve.singleObjOppEquiv G n).symm g) := by
  let N := CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)
  let s := (CategoryTheory.nerve.singleObjOppEquiv G n).symm g
  let e : ModuleCat.of k ((Fin n → G) →₀ k) ≅ ModuleCat.of k (N _⦋n⦌ →₀ k) :=
    (Finsupp.domLCongr (CategoryTheory.nerve.singleObjOppEquiv G n).symm).toModuleIso
  let F := SSet.chainComplexFreeIso N k n
  have he : ModuleCat.ofHom (Finsupp.lsingle g) ≫ e.hom =
      ModuleCat.ofHom (Finsupp.lsingle s) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Finsupp.domLCongr (R := k) (M := k)
      (CategoryTheory.nerve.singleObjOppEquiv G n).symm
      (Finsupp.single g a) = Finsupp.single s a
    simp [s]
  have hF : N.ιChainComplex s ≫ F.hom = ModuleCat.ofHom (Finsupp.lsingle s) :=
    SSet.ιChainComplex_comp_chainComplexFreeIso_hom N k n s
  have hdef : trivialOppositeNerveChainObjIso k G n = e ≪≫ F.symm := rfl
  apply (cancel_mono F.hom).mp
  rw [hdef]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact he.trans hF.symm

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The simplex inclusion at (e_n^op)⁻¹(g) followed by the inverse
degree comparison is the inhomogeneous basis inclusion at g. -/
theorem trivialOppositeNerveChainObjIso_inv_generator (n : ℕ) (g : Fin n → G) :
    (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k))
        ((CategoryTheory.nerve.singleObjOppEquiv G n).symm g) ≫
      (trivialOppositeNerveChainObjIso k G n).inv =
        ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) := by
  rw [← trivialOppositeNerveChainObjIso_generator k G n g]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem trivialBarGenerator_d (n : ℕ) (g : Fin (n + 1) → G) :
    ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) ≫
        (inhomogeneousChains (Rep.trivial k G k)).d (n + 1) n =
      ModuleCat.ofHom (Finsupp.lsingle (Fin.tail g) (R := k) (M := k)) +
        ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.val + 1)) •
          ModuleCat.ofHom (Finsupp.lsingle (Fin.contractNth j (· * ·) g)
            (R := k) (M := k)) := by
  rw [inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply]
  change inhomogeneousChains.d (Rep.trivial k G k) n (Finsupp.single g a) = _
  rw [inhomogeneousChains.d_single]
  simp [Representation.isTrivial_apply, ← Int.cast_smul_eq_zsmul k]
  rfl

private theorem trivialOppositeNerveChainObjIso_d (n : ℕ) :
    (trivialOppositeNerveChainObjIso k G (n + 1)).hom ≫
        ((CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).chainComplex
          (ModuleCat.of k k : ModuleCat.{u} k)).d
          (n + 1) n =
      (inhomogeneousChains (Rep.trivial k G k)).d (n + 1) n ≫
        (trivialOppositeNerveChainObjIso k G n).hom := by
  apply inhomogeneousChains.ext
  intro g
  let N := CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)
  let R := (ModuleCat.of k k : ModuleCat.{u} k)
  let s := (CategoryTheory.nerve.singleObjOppEquiv G (n + 1)).symm g
  calc
    ModuleCat.ofHom (Finsupp.lsingle g) ≫
        ((trivialOppositeNerveChainObjIso k G (n + 1)).hom ≫ (N.chainComplex R).d (n + 1) n) =
        N.ιChainComplex s ≫ (N.chainComplex R).d (n + 1) n := by
      rw [← Category.assoc, trivialOppositeNerveChainObjIso_generator]
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • N.ιChainComplex (N.δ i s) :=
      SSet.ιChainComplex_d (X := N) (R := R) s
    _ = N.ιChainComplex
          ((CategoryTheory.nerve.singleObjOppEquiv G n).symm (Fin.tail g)) +
        ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.val + 1)) • N.ιChainComplex
          ((CategoryTheory.nerve.singleObjOppEquiv G n).symm
            (Fin.contractNth j (· * ·) g)) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
      simp only [N, s, oppositeNerveFace_zero, oppositeNerveFace_succ]
    _ = (ModuleCat.ofHom (Finsupp.lsingle (Fin.tail g)) +
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.val + 1)) •
            ModuleCat.ofHom (Finsupp.lsingle (Fin.contractNth j (· * ·) g))) ≫
          (trivialOppositeNerveChainObjIso k G n).hom := by
      dsimp only [N]
      simp only [Preadditive.add_comp, Preadditive.sum_comp, Preadditive.zsmul_comp,
        trivialOppositeNerveChainObjIso_generator]
    _ = ModuleCat.ofHom (Finsupp.lsingle g) ≫
        ((inhomogeneousChains (Rep.trivial k G k)).d (n + 1) n ≫
          (trivialOppositeNerveChainObjIso k G n).hom) := by
      rw [← Category.assoc, trivialBarGenerator_d]

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The degreewise coordinate comparisons form the chain isomorphism
C_*(G,k_triv)≅C_*(B(Gᵐᵒᵖ);k), preserving all boundary maps. -/
def trivialOppositeNerveChainIso :
    inhomogeneousChains (Rep.trivial k G k) ≅
      (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).chainComplex (ModuleCat.of k k : ModuleCat.{u} k) :=
  HomologicalComplex.Hom.isoOfComponents (trivialOppositeNerveChainObjIso k G) (by
    rintro i j rfl
    exact trivialOppositeNerveChainObjIso_d k G j)

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The forward chain map in degree n is the corresponding
opposite-nerve coordinate isomorphism. -/
@[simp]
theorem trivialOppositeNerveChainIso_hom_f (n : ℕ) :
    (trivialOppositeNerveChainIso k G).hom.f n =
      (trivialOppositeNerveChainObjIso k G n).hom := rfl

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The inverse chain map in degree n is the inverse
opposite-nerve coordinate isomorphism. -/
@[simp]
theorem trivialOppositeNerveChainIso_inv_f (n : ℕ) :
    (trivialOppositeNerveChainIso k G).inv.f n =
      (trivialOppositeNerveChainObjIso k G n).inv := rfl

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The chain isomorphism C_*(G,k_triv)≅C_*(BG;k) is the
opposite-nerve comparison followed by the nerve map induced by inversion. -/
def trivialNerveChainIso :
    inhomogeneousChains (Rep.trivial k G k) ≅
      (CategoryTheory.nerve (SingleObj G)).chainComplex
        (ModuleCat.of k k : ModuleCat.{u} k) :=
  trivialOppositeNerveChainIso k G ≪≫
    ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj
      (ModuleCat.of k k : ModuleCat.{u} k)).mapIso (CategoryTheory.nerve.inversionIso G)

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
Taking degree n homology gives H_n(G,k_triv)≅H_n(BG;k)
through the direct-nerve chain isomorphism. -/
def trivialNerveHomologyIso (n : ℕ) :
    groupHomology (Rep.trivial k G k) n ≅
      (CategoryTheory.nerve (SingleObj G)).homology
        (ModuleCat.of k k : ModuleCat.{u} k) n :=
  HomologicalComplex.homologyMapIso (trivialNerveChainIso k G) n

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
The direct-nerve comparison sends the tuple basis g to the
simplex inclusion at e_n⁻¹(i↦g_i⁻¹).
The tuple order is retained and every group entry is inverted. -/
theorem trivialNerveChainIso_generator (n : ℕ) (g : Fin n → G) :
    ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) ≫
        (trivialNerveChainIso k G).hom.f n =
      (CategoryTheory.nerve (SingleObj G)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k))
        ((CategoryTheory.nerve.singleObjEquiv G n).symm (fun i => (g i)⁻¹)) := by
  change ModuleCat.ofHom (Finsupp.lsingle g) ≫
      ((trivialOppositeNerveChainObjIso k G n).hom ≫
        (SSet.chainComplexMap (CategoryTheory.nerve.inversionIso G).hom
          (ModuleCat.of k k : ModuleCat.{u} k)).f n) = _
  rw [← Category.assoc, trivialOppositeNerveChainObjIso_generator]
  let s : (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)) _⦋n⦌ :=
    (CategoryTheory.nerve.singleObjOppEquiv G n).symm g
  have h := SSet.ι_chainComplexMap_f
    (X := CategoryTheory.nerve (SingleObj Gᵐᵒᵖ))
    (Y := CategoryTheory.nerve (SingleObj G)) (f := (CategoryTheory.nerve.inversionIso G).hom)
    (R := (ModuleCat.of k k : ModuleCat.{u} k)) s
  exact h.trans (congrArg
    (fun t : (CategoryTheory.nerve (SingleObj G)) _⦋n⦌ =>
      (CategoryTheory.nerve (SingleObj G)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k)) t)
    (CategoryTheory.nerve.inversionIso_simplex G n g))

private theorem directNerveMap_simplex {H : Type u} [Group H]
    (f : G →* H) (n : ℕ) (g : Fin n → G) :
    (CategoryTheory.nerveMap (SingleObj.mapHom _ _ f)).app (Opposite.op ⦋n⦌)
        ((CategoryTheory.nerve.singleObjEquiv G n).symm g) =
      (CategoryTheory.nerve.singleObjEquiv H n).symm (fun i => f (g i)) := by
  apply (CategoryTheory.nerve.singleObjEquiv H n).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change f (((CategoryTheory.nerve.singleObjEquiv G n).symm g).map'
      i.val (i.val + 1)) = f (g i)
  rw [CategoryTheory.nerve.singleObjEquiv_symm_map_succ]

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
For a group homomorphism f:G→H with H in universe u,
the chain comparison obeys
nerveChains(f)∘comparison_G=comparison_H∘groupChains(f). -/
theorem trivialNerveChainIso_hom_naturality {H : Type u} [Group H] (f : G →* H) :
    chainsMap f (𝟙 (Rep.trivial k G k) : Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k)) ≫
        (trivialNerveChainIso k H).hom =
      (trivialNerveChainIso k G).hom ≫
        SSet.chainComplexMap (CategoryTheory.nerveMap (SingleObj.mapHom _ _ f))
          (ModuleCat.of k k : ModuleCat.{u} k) := by
  ext n : 1
  apply inhomogeneousChains.ext
  intro g
  let R := (ModuleCat.of k k : ModuleCat.{u} k)
  let F := CategoryTheory.nerveMap (SingleObj.mapHom _ _ f)
  calc
    ModuleCat.ofHom (Finsupp.lsingle g) ≫
        ((chainsMap f (𝟙 (Rep.trivial k G k) :
            Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k))).f n ≫
          (trivialNerveChainIso k H).hom.f n) =
        ModuleCat.ofHom (Finsupp.lsingle (f ∘ g)) ≫
          (trivialNerveChainIso k H).hom.f n := by
      have hsingle := lsingle_comp_chainsMap_f
        (A := Rep.trivial k G k) (B := Rep.trivial k H k) f
        (𝟙 (Rep.trivial k G k) : Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k)) n g
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ (trivialNerveChainIso k H).hom.f n) hsingle)
    _ = (CategoryTheory.nerve (SingleObj H)).ιChainComplex
        ((CategoryTheory.nerve.singleObjEquiv H n).symm (fun i => (f (g i))⁻¹)) :=
      trivialNerveChainIso_generator k H n (f ∘ g)
    _ = (CategoryTheory.nerve (SingleObj G)).ιChainComplex
        ((CategoryTheory.nerve.singleObjEquiv G n).symm (fun i => (g i)⁻¹)) ≫
          (SSet.chainComplexMap F R).f n := by
      let s : (CategoryTheory.nerve (SingleObj G)) _⦋n⦌ :=
        (CategoryTheory.nerve.singleObjEquiv G n).symm (fun i => (g i)⁻¹)
      have hmap := SSet.ι_chainComplexMap_f
        (X := CategoryTheory.nerve (SingleObj G))
        (Y := CategoryTheory.nerve (SingleObj H)) (f := F) (R := R) s
      have hval : F.app (Opposite.op ⦋n⦌) s =
          (CategoryTheory.nerve.singleObjEquiv H n).symm
            (fun i => (f (g i))⁻¹) := by
        exact (directNerveMap_simplex G f n (fun i => (g i)⁻¹)).trans
          (congrArg (CategoryTheory.nerve.singleObjEquiv H n).symm
            (by funext i; exact map_inv f (g i)))
      exact (hmap.trans (congrArg
        (fun t : (CategoryTheory.nerve (SingleObj H)) _⦋n⦌ =>
          (CategoryTheory.nerve (SingleObj H)).ιChainComplex (R := R) t) hval)).symm
    _ = ModuleCat.ofHom (Finsupp.lsingle g) ≫
        ((trivialNerveChainIso k G).hom.f n ≫ (SSet.chainComplexMap F R).f n) := by
      rw [← Category.assoc, trivialNerveChainIso_generator]

/-- Let k be a commutative ring and G a group in universe u. Coefficients are k_triv. Let e_n^op and
e_n be the
coordinate equivalences from n-simplices of the one-object nerves
B(Gᵐᵒᵖ) and BG to ordered G^n tuples.
For f:G→H and n∈ℕ, the homology comparisons satisfy
nerveH_n(f)∘comparison_G=comparison_H∘groupH_n(f). -/
theorem trivialNerveHomologyIso_hom_naturality {H : Type u} [Group H]
    (f : G →* H) (n : ℕ) :
    groupHomology.map f
        (𝟙 (Rep.trivial k G k) : Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k)) n ≫
        (trivialNerveHomologyIso k H n).hom =
      (trivialNerveHomologyIso k G n).hom ≫
        SSet.homologyMap (CategoryTheory.nerveMap (SingleObj.mapHom _ _ f))
          (ModuleCat.of k k : ModuleCat.{u} k) n := by
  change HomologicalComplex.homologyMap
      (chainsMap f
        (𝟙 (Rep.trivial k G k) : Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k))) n ≫
      HomologicalComplex.homologyMap (trivialNerveChainIso k H).hom n =
    HomologicalComplex.homologyMap (trivialNerveChainIso k G).hom n ≫
      HomologicalComplex.homologyMap
        (SSet.chainComplexMap (CategoryTheory.nerveMap (SingleObj.mapHom _ _ f))
          (ModuleCat.of k k : ModuleCat.{u} k)) n
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun c => HomologicalComplex.homologyMap c n)
      (trivialNerveChainIso_hom_naturality k G f)

end Chains

end groupHomology

end
