/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.ModuleCat.Prod.Decomposition
import MathlibExt.Algebra.Category.ModuleCat.Prod.FstAdjunctions
import MathlibExt.Algebra.Category.ModuleCat.Prod.SndAdjunctions
import MathlibExt.Algebra.Category.FGModuleCat.Prod.Components
import MathlibExt.Algebra.Category.FGModuleCat.Prod.Embeddings
import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorLeft
import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Concrete clients of the product-ring and balanced-tensor module APIs

Every example below runs the public API on explicit rings and rank-one modules, with all
class hypotheses discharged by stock instances and every computed value checked.

* The regular module of `ℤ × ℚ` splits as `ℤ × 0` and `0 × ℚ`: membership, projections,
  inclusions, the decomposition equivalence, the component functors on an explicit
  multiplication map, the biproduct decomposition, and the embedding/component isomorphisms.
* All four product-ring adjunctions are evaluated on `ℤ`, `ℚ` and `ℤ × ℚ`; the unit of
  `eComponentFunctor ⊣ prodEmbeddingFst` really discards the nonzero `ℚ` coordinate.
* `RingHom.fst ℤ ℚ` and `RingHom.snd ℤ ℚ` are finite restrictions, giving finitely generated
  embeddings; the components of the finitely generated regular module are finitely generated
  over `ℤ` and over `ℚ`, and the finitely generated component functors are computed.
* The balanced tensor over `ℚ × ℚ` identifies `(1,0) ⊗ (0,1)` with `0` but not
  `(1,0) ⊗ (1,0)`; its functor, outer left module and ground comparison are computed on
  explicit elements, and extension of scalars along `ℤ → ℚ` is additive on explicit maps.
* Same-ring boundary: over `ℚ × ℚ` the `e`-component carries both the API `ℚ`-module (through
  `(r, 0)`) and the restricted diagonal one; they agree. Over `ℤ × ℚ` the API `ℤ`-module agrees
  with the canonical one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ProdIdempotent MulOpposite
open scoped TensorProduct ChangeOfRings

namespace MathlibExtTest.ProductRingTensorClients

/-! ## The idempotent decomposition of the regular `ℤ × ℚ`-module -/

theorem five_mem_e : ((5 : ℤ), (0 : ℚ)) ∈ eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ) := by
  rw [mem_eSubmodule_iff]
  simp [ProdIdempotent.e]

theorem half_mem_f : ((0 : ℤ), (1 / 2 : ℚ)) ∈ fSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ) := by
  rw [mem_fSubmodule_iff]
  simp [ProdIdempotent.f]

/-- The two components are different: `(0, 1/2)` is not in the `e`-component. -/
example : ((0 : ℤ), (1 / 2 : ℚ)) ∉ eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ) := by
  rw [mem_eSubmodule_iff]
  simp [ProdIdempotent.e]

example : ((5 : ℤ), (0 : ℚ)) ∉ fSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ) := by
  rw [mem_fSubmodule_iff]
  simp [ProdIdempotent.f]

/-- The decomposition of `(3, 2/5)` has the distinct nonzero parts `(3,0)` and `(0,2/5)`. -/
example :
    ((decompEquiv (R := ℤ) (S := ℚ) (M := ℤ × ℚ) ((3 : ℤ), (2 / 5 : ℚ))).1 : ℤ × ℚ) =
        ((3 : ℤ), (0 : ℚ)) ∧
      ((decompEquiv (R := ℤ) (S := ℚ) (M := ℤ × ℚ) ((3 : ℤ), (2 / 5 : ℚ))).2 : ℤ × ℚ) =
        ((0 : ℤ), (2 / 5 : ℚ)) := by
  rw [decompEquiv_apply]
  constructor
  · change ProdIdempotent.e ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) = _
    simp [ProdIdempotent.e]
  · change ProdIdempotent.f ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) = _
    simp [ProdIdempotent.f]

example :
    (decompEquiv (R := ℤ) (S := ℚ) (M := ℤ × ℚ)).symm (⟨_, five_mem_e⟩, ⟨_, half_mem_f⟩) =
      ((5 : ℤ), (1 / 2 : ℚ)) := by
  rw [decompEquiv_symm_apply]
  simp

/-- Projection then inclusion is multiplication by `e`; the opposite projection vanishes. -/
example :
    eIncl (R := ℤ) (S := ℚ) (eProj (R := ℤ) (S := ℚ) (M := ℤ × ℚ) ((3 : ℤ), (2 / 5 : ℚ))) =
      ((3 : ℤ), (0 : ℚ)) := by
  rw [eIncl_eProj]
  simp [ProdIdempotent.e]

example : fProj (R := ℤ) (S := ℚ) (M := ℤ × ℚ) (eIncl (R := ℤ) (S := ℚ) ⟨_, five_mem_e⟩) = 0 :=
  fProj_eIncl _

example : eProj (R := ℤ) (S := ℚ) (M := ℤ × ℚ) (fIncl (R := ℤ) (S := ℚ) ⟨_, half_mem_f⟩) = 0 :=
  eProj_fIncl _

/-- Mutation check: the `e`-projection does not return the `ℚ`-coordinate. -/
example :
    (eProj (R := ℤ) (S := ℚ) (M := ℤ × ℚ) ((3 : ℤ), (2 / 5 : ℚ)) : ℤ × ℚ) ≠
      ((0 : ℤ), (2 / 5 : ℚ)) := by
  change ProdIdempotent.e ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) ≠ _
  simp [ProdIdempotent.e]

/-- The API `ℤ`-action on the `e`-component is through `(r, 0)`. -/
example :
    ((@HSMul.hSMul ℤ _ _ (@instHSMul ℤ _ instSMulR_eSubmodule) (2 : ℤ) ⟨_, five_mem_e⟩ :
        eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) : ℤ × ℚ) = ((10 : ℤ), (0 : ℚ)) := by
  rw [coe_smulR_eSubmodule]
  simp

/-- The API `ℚ`-action on the `f`-component is through `(0, s)`. -/
example :
    ((@HSMul.hSMul ℚ _ _ (@instHSMul ℚ _ instSMulS_fSubmodule) (4 : ℚ) ⟨_, half_mem_f⟩ :
        fSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) : ℤ × ℚ) = ((0 : ℤ), (2 : ℚ)) := by
  rw [coe_smulS_fSubmodule]
  norm_num

/-! ## Same-ring boundary -/

/-- Over `ℤ × ℚ` the API `ℤ`-module on the `e`-component is the canonical one. -/
example :
    @Eq (Module ℤ (eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)))
      (instModuleR_eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ))
      (AddCommGroup.toIntModule (eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ))) :=
  Subsingleton.elim _ _

/-- Instance resolution at `R = ℤ` selects the canonical `ℤ`-module, not the API one; the
previous example is what makes the two interchangeable. -/
example :
    (inferInstance : Module ℤ (eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ))) =
      AddCommGroup.toIntModule _ :=
  rfl

/-- Over `ℚ × ℚ` the `e`-component has two `ℚ`-modules: the API one through `(r, 0)` and the
restriction of the diagonal action. They are equal. -/
example :
    (instModuleR_eSubmodule (R := ℚ) (S := ℚ) (M := ℚ × ℚ)) =
      Submodule.module' (eSubmodule (R := ℚ) (S := ℚ) (M := ℚ × ℚ)) := by
  apply Module.ext'
  rintro r ⟨⟨a, b⟩, hx⟩
  have hb : b = 0 := by
    have h := (mem_eSubmodule_iff (R := ℚ) (S := ℚ) (M := ℚ × ℚ) (a, b)).mp hx
    have h2 := congrArg Prod.snd h
    simp [ProdIdempotent.e] at h2
    exact h2.symm
  subst hb
  apply Subtype.ext
  change ((r, (0 : ℚ)) • ((a, (0 : ℚ)) : ℚ × ℚ)) = r • ((a, (0 : ℚ)) : ℚ × ℚ)
  simp

/-! ## The component functors, the decomposition and the embeddings -/

/-- An element of the `e`-component of the regular module, read as a pair. -/
abbrev eVal (x : eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) : ℤ × ℚ := x

/-- An element of the `f`-component of the regular module, read as a pair. -/
abbrev fVal (x : fSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) : ℤ × ℚ := x

/-- The regular module of `ℤ × ℚ`. -/
abbrev reg : ModuleCat.{0} (ℤ × ℚ) := ModuleCat.of (ℤ × ℚ) (ℤ × ℚ)

/-- Multiplication by `(2, 3)` on the regular module. -/
abbrev twoThree : reg ⟶ reg := ModuleCat.ofHom (LinearMap.mulLeft (ℤ × ℚ) ((2, 3) : ℤ × ℚ))

/-- Multiplication by `(1, -1)` on the regular module. -/
abbrev oneNegOne : reg ⟶ reg := ModuleCat.ofHom (LinearMap.mulLeft (ℤ × ℚ) ((1, -1) : ℤ × ℚ))

example :
    eVal (((eComponentFunctor (R := ℤ) (S := ℚ)).map twoThree).hom ⟨_, five_mem_e⟩) =
      ((10 : ℤ), (0 : ℚ)) := by
  change ((2, 3) : ℤ × ℚ) * ((5 : ℤ), (0 : ℚ)) = _
  norm_num

example :
    fVal (((fComponentFunctor (R := ℤ) (S := ℚ)).map twoThree).hom ⟨_, half_mem_f⟩) =
      ((0 : ℤ), (3 / 2 : ℚ)) := by
  change ((2, 3) : ℤ × ℚ) * ((0 : ℤ), (1 / 2 : ℚ)) = _
  norm_num

/-- The component functors are additive on an explicit sum of multiplication maps. -/
example :
    (eComponentFunctor (R := ℤ) (S := ℚ)).map (twoThree + oneNegOne) =
      (eComponentFunctor (R := ℤ) (S := ℚ)).map twoThree +
        (eComponentFunctor (R := ℤ) (S := ℚ)).map oneNegOne :=
  (eComponentFunctor_additive (R := ℤ) (S := ℚ)).map_add

example :
    fVal (((fComponentFunctor (R := ℤ) (S := ℚ)).map (twoThree + oneNegOne)).hom
        ⟨_, half_mem_f⟩) = ((0 : ℤ), (1 : ℚ)) := by
  rw [(fComponentFunctor_additive (R := ℤ) (S := ℚ)).map_add]
  change ((2, 3) : ℤ × ℚ) * ((0 : ℤ), (1 / 2 : ℚ)) +
      ((1, -1) : ℤ × ℚ) * ((0 : ℤ), (1 / 2 : ℚ)) = _
  norm_num

/-- The biproduct decomposition projects `(3, 2/5)` to its `e`-part `(3, 0)`. -/
example :
    (((decompBiprodIso ℤ ℚ reg).hom ≫ biprod.fst).hom ((3 : ℤ), (2 / 5 : ℚ)) : ℤ × ℚ) =
      ((3 : ℤ), (0 : ℚ)) := by
  rw [decompBiprodIso, Iso.trans_hom, Category.assoc, prodToBiprodIso, Iso.symm_hom,
    ModuleCat.biprodIsoProd_inv_comp_fst]
  change ProdIdempotent.e ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) = _
  simp [ProdIdempotent.e]

example :
    (((decompBiprodIso ℤ ℚ reg).hom ≫ biprod.snd).hom ((3 : ℤ), (2 / 5 : ℚ)) : ℤ × ℚ) =
      ((0 : ℤ), (2 / 5 : ℚ)) := by
  rw [decompBiprodIso, Iso.trans_hom, Category.assoc, prodToBiprodIso, Iso.symm_hom,
    ModuleCat.biprodIsoProd_inv_comp_snd]
  change ProdIdempotent.f ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) = _
  simp [ProdIdempotent.f]

/-- Reassembling the two components through the embedded biproduct recovers `(5, 1/2)`. -/
example :
    (prodDecompositionIso (M := reg)).inv.hom
        ((biprod.mapIso (eSubmoduleIsoEmbeddingFst reg) (fSubmoduleIsoEmbeddingSnd reg)).hom.hom
          ((prodToBiprodIso ℤ ℚ reg).hom.hom (⟨_, five_mem_e⟩, ⟨_, half_mem_f⟩))) =
      ((5 : ℤ), (1 / 2 : ℚ)) := by
  rw [prodDecompositionIso_inv_apply]
  simp

/-- The rank-one `ℤ`-module, the rank-one `ℚ`-module. -/
abbrev intLine : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

abbrev ratLine : ModuleCat.{0} ℚ := ModuleCat.of ℚ ℚ

/-- `ℤ × ℚ` acts on the `fst`-embedded `ℤ` through the first coordinate, and on the
`snd`-embedded `ℚ` through the second. -/
example :
    (((3 : ℤ), (7 / 2 : ℚ)) • (show (ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine from (5 : ℤ)) :
      (ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine) = (15 : ℤ) := by
  rw [ModuleCat.prodEmbeddingFst_smul_def]
  rfl

example :
    (((3 : ℤ), (7 / 2 : ℚ)) • (show (ModuleCat.prodEmbeddingSnd ℤ ℚ).obj ratLine from (2 : ℚ)) :
      (ModuleCat.prodEmbeddingSnd ℤ ℚ).obj ratLine) = (7 : ℚ) := by
  rw [ModuleCat.prodEmbeddingSnd_smul_def]
  change (7 / 2 : ℚ) * 2 = 7
  norm_num

/-- The `e`-component of the `fst`-embedded line is everything; the comparison isomorphism
returns the original element. -/
example : eSubmodule (R := ℤ) (S := ℚ) (M := (ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine) = ⊤ :=
  eSubmodule_prodEmbeddingFst_eq_top intLine

example :
    (prodEmbeddingFst_eComponentIso (R := ℤ) (S := ℚ) intLine).hom.hom
        ⟨(5 : ℤ), by rw [eSubmodule_prodEmbeddingFst_eq_top intLine]; trivial⟩ = (5 : ℤ) :=
  rfl

/-- The `f`-component of the `fst`-embedded line is zero (isomorphic to `PUnit`). -/
example (x : fSubmoduleAsModuleCat (R := ℤ) (S := ℚ)
    ((ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine)) : x = 0 :=
  (prodEmbeddingFst_fComponentZeroIso (R := ℤ) (S := ℚ) intLine).toLinearEquiv.injective rfl

/-- Symmetrically, the `f`-component of the `snd`-embedded `ℚ` is that line, and its
`e`-component is zero. -/
example :
    (prodEmbeddingSnd_fComponentIso (R := ℤ) (S := ℚ) ratLine).hom.hom
        ⟨(2 / 7 : ℚ), by rw [fSubmodule_prodEmbeddingSnd_eq_top ratLine]; trivial⟩ =
      (2 / 7 : ℚ) :=
  rfl

example (x : eSubmoduleAsModuleCat (R := ℤ) (S := ℚ)
    ((ModuleCat.prodEmbeddingSnd ℤ ℚ).obj ratLine)) : x = 0 :=
  (prodEmbeddingSnd_eComponentZeroIso (R := ℤ) (S := ℚ) ratLine).toLinearEquiv.injective rfl

/-! ## All four product-ring adjunctions, evaluated -/

/-- The `(ℤ × ℚ)`-linear inclusion of the `fst`-embedded line as `n ↦ (n, 0)`. -/
def lineToReg : (ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine ⟶ reg :=
  ModuleCat.ofHom (X := (ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine) (Y := ℤ × ℚ)
    { toFun := fun n => ((show ℤ from n), (0 : ℚ))
      map_add' := by
        intro a b
        ext <;> simp
        rfl
      map_smul' := by
        intro p n
        ext
        · change p.1 * (show ℤ from n) = p.1 * (show ℤ from n)
          rfl
        · simp }

example :
    eVal (((prodEmbeddingFstAdj_eComponentFunctor ℤ ℚ).homEquiv intLine reg lineToReg).hom
        (7 : ℤ)) = ((7 : ℤ), (0 : ℚ)) :=
  rfl

example :
    (((prodEmbeddingFstAdj_eComponentFunctor ℤ ℚ).counit.app reg).hom ⟨_, five_mem_e⟩ :
      ℤ × ℚ) = ((5 : ℤ), (0 : ℚ)) :=
  rfl

/-- The unit of `eComponentFunctor ⊣ prodEmbeddingFst` keeps `3` and discards `2/5`. -/
example :
    eVal (((eComponentFunctorAdj_prodEmbeddingFst ℤ ℚ).unit.app reg).hom
        ((3 : ℤ), (2 / 5 : ℚ))) = ((3 : ℤ), (0 : ℚ)) := by
  change ProdIdempotent.e ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) = _
  simp [ProdIdempotent.e]

example :
    ((eComponentFunctorAdj_prodEmbeddingFst ℤ ℚ).counit.app intLine).hom
        ⟨(5 : ℤ), by rw [eSubmodule_prodEmbeddingFst_eq_top intLine]; trivial⟩ = (5 : ℤ) :=
  rfl

/-- Transposing the computed map `eComponentFunctor.map (2, 3)` along
`eComponentFunctor ⊣ prodEmbeddingFst` multiplies the `e`-part of `(3, 2/5)` by `2`. -/
example :
    eVal (((eComponentFunctorAdj_prodEmbeddingFst ℤ ℚ).homEquiv reg
        ((eComponentFunctor (R := ℤ) (S := ℚ)).obj reg)
          ((eComponentFunctor (R := ℤ) (S := ℚ)).map twoThree)).hom ((3 : ℤ), (2 / 5 : ℚ))) =
      ((6 : ℤ), (0 : ℚ)) := by
  rw [Adjunction.homEquiv_unit]
  change ((2, 3) : ℤ × ℚ) * (ProdIdempotent.e ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ))) = _
  norm_num [ProdIdempotent.e]

/-- The `(ℤ × ℚ)`-linear inclusion of the `snd`-embedded line as `q ↦ (0, q)`. -/
def ratToReg : (ModuleCat.prodEmbeddingSnd ℤ ℚ).obj ratLine ⟶ reg :=
  ModuleCat.ofHom (X := (ModuleCat.prodEmbeddingSnd ℤ ℚ).obj ratLine) (Y := ℤ × ℚ)
    { toFun := fun q => ((0 : ℤ), (show ℚ from q))
      map_add' := by
        intro a b
        ext <;> simp
        rfl
      map_smul' := by
        intro p q
        ext
        · simp
        · change p.2 * (show ℚ from q) = p.2 * (show ℚ from q)
          rfl }

example :
    fVal (((prodEmbeddingSndAdj_fComponentFunctor ℤ ℚ).homEquiv ratLine reg ratToReg).hom
        (2 / 7 : ℚ)) = ((0 : ℤ), (2 / 7 : ℚ)) :=
  rfl

/-- The unit of `fComponentFunctor ⊣ prodEmbeddingSnd` keeps `2/5` and discards `3`. -/
example :
    fVal (((fComponentFunctorAdj_prodEmbeddingSnd ℤ ℚ).unit.app reg).hom
        ((3 : ℤ), (2 / 5 : ℚ))) = ((0 : ℤ), (2 / 5 : ℚ)) := by
  change ProdIdempotent.f ℤ ℚ • ((3 : ℤ), (2 / 5 : ℚ)) = _
  simp [ProdIdempotent.f]

example :
    (((prodEmbeddingSndAdj_fComponentFunctor ℤ ℚ).counit.app reg).hom ⟨_, half_mem_f⟩ :
      ℤ × ℚ) = ((0 : ℤ), (1 / 2 : ℚ)) :=
  rfl

example :
    ((fComponentFunctorAdj_prodEmbeddingSnd ℤ ℚ).counit.app ratLine).hom
        ⟨(2 / 7 : ℚ), by rw [fSubmodule_prodEmbeddingSnd_eq_top ratLine]; trivial⟩ =
      (2 / 7 : ℚ) :=
  rfl

/-! ## Finite restriction along `fst` and finitely generated components -/

/-- `ℤ` is finite over `ℤ × ℚ` through `fst`, by the API proof. -/
example : (RingHom.fst ℤ ℚ).IsFinite := RingHom.isFinite_fst

example : @Module.Finite (ℤ × ℚ) ℤ _ _ (Module.compHom ℤ (RingHom.fst ℤ ℚ)) :=
  FGModuleCat.finite_of_finite (RingHom.fst ℤ ℚ) RingHom.isFinite_fst ℤ

/-- The finitely generated `fst`-embedding of `ℤ`: its finiteness over `ℤ × ℚ` is derived. -/
example : Module.Finite (ℤ × ℚ) ((ModuleCat.prodEmbeddingFst ℤ ℚ).obj intLine) :=
  ((FGModuleCat.prodEmbeddingFst ℤ ℚ).obj (FGModuleCat.of ℤ ℤ)).property

example :
    (((3 : ℤ), (7 / 2 : ℚ)) •
        (show (FGModuleCat.prodEmbeddingFst ℤ ℚ).obj (FGModuleCat.of ℤ ℤ) from (5 : ℤ)) :
      (FGModuleCat.prodEmbeddingFst ℤ ℚ).obj (FGModuleCat.of ℤ ℤ)) = (15 : ℤ) := by
  rw [FGModuleCat.prodEmbeddingFst_smul_def]
  rfl

/-- Multiplication by `-4` on the finitely generated line, and its image under the embedding. -/
abbrev negFour : FGModuleCat.of ℤ ℤ ⟶ FGModuleCat.of ℤ ℤ :=
  FGModuleCat.ofHom ((-4 : ℤ) • LinearMap.id)

example :
    (FGModuleCat.prodEmbeddingFst ℤ ℚ).map negFour (show (FGModuleCat.of ℤ ℤ) from (5 : ℤ)) =
      (-20 : ℤ) := by
  rw [FGModuleCat.prodEmbeddingFst_map_apply]
  rfl

/-- The finitely generated regular module of `ℤ × ℚ`. -/
abbrev fgReg : FGModuleCat.{0} (ℤ × ℚ) := FGModuleCat.of (ℤ × ℚ) (ℤ × ℚ)

/-- Its `e`-component `ℤ × 0` is finite over `ℤ` and its `f`-component `0 × ℚ` is finite over
`ℚ`, both derived by the API. -/
example : ModuleCat.isFG ℤ (eSubmoduleAsModuleCat (R := ℤ) (S := ℚ) reg) :=
  ((eComponentFunctorFG (R := ℤ) (S := ℚ)).obj fgReg).property

example : Module.Finite ℚ (fSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) :=
  ((fComponentFunctorFG (R := ℤ) (S := ℚ)).obj fgReg).property

/-- Through the same-ring boundary the API finiteness of `ℤ × 0` is finiteness for the
canonical `ℤ`-module. -/
example : Module.Finite ℤ (eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) := by
  have h : @Module.Finite ℤ (eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) _ _
      (instModuleR_eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)) :=
    ((eComponentFunctorFG (R := ℤ) (S := ℚ)).obj fgReg).property
  have hm : @Eq (Module ℤ (eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ)))
      (instModuleR_eSubmodule (R := ℤ) (S := ℚ) (M := ℤ × ℚ))
      (AddCommGroup.toIntModule _) := Subsingleton.elim _ _
  rw [hm] at h
  exact h

/-- Multiplication by `(2, 3)` and by `(1, -1)` on the finitely generated regular module. -/
abbrev fgTwoThree : fgReg ⟶ fgReg :=
  FGModuleCat.ofHom (LinearMap.mulLeft (ℤ × ℚ) ((2, 3) : ℤ × ℚ))

abbrev fgOneNegOne : fgReg ⟶ fgReg :=
  FGModuleCat.ofHom (LinearMap.mulLeft (ℤ × ℚ) ((1, -1) : ℤ × ℚ))

example :
    eVal (((eComponentFunctorFG (R := ℤ) (S := ℚ)).map fgTwoThree).hom.hom ⟨_, five_mem_e⟩) =
      ((10 : ℤ), (0 : ℚ)) := by
  rw [eComponentFunctorFG_map_hom_hom]
  change ((2, 3) : ℤ × ℚ) * ((5 : ℤ), (0 : ℚ)) = _
  norm_num

example :
    fVal (((fComponentFunctorFG (R := ℤ) (S := ℚ)).map fgTwoThree).hom.hom ⟨_, half_mem_f⟩) =
      ((0 : ℤ), (3 / 2 : ℚ)) := by
  rw [fComponentFunctorFG_map_hom_hom]
  change ((2, 3) : ℤ × ℚ) * ((0 : ℤ), (1 / 2 : ℚ)) = _
  norm_num

/-- The finitely generated component functors are additive on an explicit sum. -/
example :
    (eComponentFunctorFG (R := ℤ) (S := ℚ)).map (fgTwoThree + fgOneNegOne) =
      (eComponentFunctorFG (R := ℤ) (S := ℚ)).map fgTwoThree +
        (eComponentFunctorFG (R := ℤ) (S := ℚ)).map fgOneNegOne :=
  (eComponentFunctorFG_additive (R := ℤ) (S := ℚ)).map_add

example :
    (fComponentFunctorFG (R := ℤ) (S := ℚ)).map (fgTwoThree + fgOneNegOne) =
      (fComponentFunctorFG (R := ℤ) (S := ℚ)).map fgTwoThree +
        (fComponentFunctorFG (R := ℤ) (S := ℚ)).map fgOneNegOne :=
  (fComponentFunctorFG_additive (R := ℤ) (S := ℚ)).map_add

/-- `ℚ` is finite over `ℤ × ℚ` through `snd`; its finitely generated embedding is computed. -/
example : (RingHom.snd ℤ ℚ).IsFinite := RingHom.isFinite_snd

example : Module.Finite (ℤ × ℚ) ((ModuleCat.prodEmbeddingSnd ℤ ℚ).obj ratLine) :=
  ((FGModuleCat.prodEmbeddingSnd ℤ ℚ).obj (FGModuleCat.of ℚ ℚ)).property

example :
    (((3 : ℤ), (7 / 2 : ℚ)) •
        (show (FGModuleCat.prodEmbeddingSnd ℤ ℚ).obj (FGModuleCat.of ℚ ℚ) from (2 : ℚ)) :
      (FGModuleCat.prodEmbeddingSnd ℤ ℚ).obj (FGModuleCat.of ℚ ℚ)) = (7 : ℚ) := by
  rw [FGModuleCat.prodEmbeddingSnd_smul_def]
  change (7 / 2 : ℚ) * 2 = 7
  norm_num

/-! ## Balanced tensors over `ℚ × ℚ` on rank-one modules

The left factor is `ℚ × ℚ` with its right regular action, the variable left module is `qq`. The
ground module that `ModuleCat.BalancedTensor.obj` installs on `qq` is passed explicitly (no
local instance), so it cannot replace the stock `ℚ`-module of the left factor. -/

/-- The rank-one left module `ℚ × ℚ` over `ℚ × ℚ`. -/
abbrev qq : ModuleCat.{0} (ℚ × ℚ) := ModuleCat.of (ℚ × ℚ) (ℚ × ℚ)

/-- Multiplication by `(2, 3)` and by `(1, 5)` on `qq`. -/
abbrev twoThreeQ : qq ⟶ qq := ModuleCat.ofHom (LinearMap.mulLeft (ℚ × ℚ) ((2, 3) : ℚ × ℚ))

abbrev oneFiveQ : qq ⟶ qq := ModuleCat.ofHom (LinearMap.mulLeft (ℚ × ℚ) ((1, 5) : ℚ × ℚ))

/-- The ground `ℚ`-module that `ModuleCat.BalancedTensor.obj` puts on `qq`: restriction along
`algebraMap ℚ (ℚ × ℚ)`. -/
abbrev groundQ : Module ℚ qq.carrier := Module.compHom qq.carrier (algebraMap ℚ (ℚ × ℚ))

/-- The balanced quotient underlying
`(ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).obj qq`. -/
abbrev Bal : Type := @TensorProduct.Balanced ℚ (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ groundQ _ _

/-- The pure class `m ⊗ n` in `Bal`. -/
abbrev bmk (m n : ℚ × ℚ) : Bal :=
  @TensorProduct.Balanced.mk ℚ (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ groundQ _ _ m n

/-- The balanced `ℚ`-bilinear map `(m, n) ↦ (m * n).1`. -/
def firstProduct : @LinearMap ℚ ℚ _ _ (RingHom.id ℚ) (ℚ × ℚ)
    (@LinearMap ℚ ℚ _ _ (RingHom.id ℚ) qq.carrier ℚ _ _ groundQ _) _ _ _ _ :=
  @LinearMap.mk₂ ℚ _ (ℚ × ℚ) qq.carrier ℚ _ _ _ _ groundQ _
    (fun m n => (m * (show ℚ × ℚ from n)).1)
    (fun m₁ m₂ n => by simp [add_mul])
    (fun c m n => by
      change ((c • m) * (show ℚ × ℚ from n)).1 = c * (m * (show ℚ × ℚ from n)).1
      simp)
    (fun m n₁ n₂ => by
      change (m * ((show ℚ × ℚ from n₁) + (show ℚ × ℚ from n₂))).1 =
        (m * (show ℚ × ℚ from n₁)).1 + (m * (show ℚ × ℚ from n₂)).1
      simp [mul_add])
    (fun c m n => by
      change (m * (algebraMap ℚ (ℚ × ℚ) c * (show ℚ × ℚ from n))).1 =
        c * (m * (show ℚ × ℚ from n)).1
      simp [Algebra.algebraMap_eq_smul_one])

/-- The functional `m ⊗ n ↦ (m * n).1` on `Bal`; it witnesses that classes are nonzero. -/
def firstCoord : Bal →ₗ[ℚ] ℚ :=
  @TensorProduct.Balanced.lift ℚ (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ groundQ _ _ ℚ _ _
    firstProduct (fun r m n => by
      change ((m * r) * (show ℚ × ℚ from n)).1 = (m * (r * (show ℚ × ℚ from n))).1
      rw [mul_assoc])

theorem firstCoord_bmk (m n : ℚ × ℚ) : firstCoord (bmk m n) = (m * n).1 :=
  rfl

/-- The balancing relation identifies `(1,0) ⊗ (0,1)` with `0`. -/
example : bmk ((1 : ℚ), (0 : ℚ)) ((0 : ℚ), (1 : ℚ)) = 0 := by
  have h := @TensorProduct.Balanced.balance ℚ (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ groundQ _ _
    ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (0 : ℚ)) ((0 : ℚ), (1 : ℚ))
  have h1 : (op ((1 : ℚ), (0 : ℚ)) • ((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) = ((1 : ℚ), (0 : ℚ)) := by
    rw [op_smul_eq_mul]
    simp
  have h2 : (((1 : ℚ), (0 : ℚ)) • (show qq.carrier from ((0 : ℚ), (1 : ℚ))) : qq.carrier) =
      0 := by
    change ((1 : ℚ), (0 : ℚ)) * ((0 : ℚ), (1 : ℚ)) = 0
    simp
  rw [h1, h2, map_zero] at h
  exact h

/-- But `(1,0) ⊗ (1,0)` is not `0`: the functional sends it to `1`. -/
example : bmk ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (0 : ℚ)) ≠ 0 := by
  intro h
  have h' := congrArg firstCoord h
  rw [firstCoord_bmk, map_zero] at h'
  norm_num at h'

/-- The balanced tensor functor on `twoThreeQ`, computed on a pure class. -/
example :
    ((ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map twoThreeQ).hom
        (bmk ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (1 : ℚ))) =
      bmk ((1 : ℚ), (0 : ℚ)) ((2 : ℚ), (3 : ℚ)) := by
  refine (ModuleCat.BalancedTensor.map_mk ℚ (ℚ × ℚ) (ℚ × ℚ) twoThreeQ _ _).trans ?_
  congr 1
  change ((2, 3) : ℚ × ℚ) * ((1 : ℚ), (1 : ℚ)) = ((2 : ℚ), (3 : ℚ))
  norm_num

/-- The computed map is neither the identity nor zero on this class: `1 ↦ 2`. -/
example :
    firstCoord (((ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map twoThreeQ).hom
        (bmk ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (1 : ℚ)))) = 2 := by
  calc _ = firstCoord (bmk ((1 : ℚ), (0 : ℚ)) (((2, 3) : ℚ × ℚ) * ((1 : ℚ), (1 : ℚ)))) :=
        congrArg firstCoord (ModuleCat.BalancedTensor.map_mk ℚ (ℚ × ℚ) (ℚ × ℚ) twoThreeQ _ _)
    _ = 2 := by
        rw [firstCoord_bmk]
        norm_num

/-- Additivity of the balanced tensor functor, evaluated on an explicit sum. -/
example :
    (ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map (twoThreeQ + oneFiveQ) =
      (ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map twoThreeQ +
        (ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map oneFiveQ :=
  (ModuleCat.BalancedTensor.additive ℚ (ℚ × ℚ) (ℚ × ℚ)).map_add

example :
    firstCoord (((ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map
        (twoThreeQ + oneFiveQ)).hom (bmk ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (1 : ℚ)))) = 3 := by
  have hadd := (ModuleCat.BalancedTensor.additive ℚ (ℚ × ℚ) (ℚ × ℚ)).map_add
    (f := twoThreeQ) (g := oneFiveQ)
  calc _ = firstCoord (((ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map twoThreeQ).hom
          (bmk ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (1 : ℚ))) +
        ((ModuleCat.BalancedTensor.functor ℚ (ℚ × ℚ) (ℚ × ℚ)).map oneFiveQ).hom
          (bmk ((1 : ℚ), (0 : ℚ)) ((1 : ℚ), (1 : ℚ)))) := by
        rw [hadd]
        rfl
    _ = firstCoord (bmk ((1 : ℚ), (0 : ℚ)) (((2, 3) : ℚ × ℚ) * ((1 : ℚ), (1 : ℚ)))) +
        firstCoord (bmk ((1 : ℚ), (0 : ℚ)) (((1, 5) : ℚ × ℚ) * ((1 : ℚ), (1 : ℚ)))) :=
        (map_add firstCoord _ _).trans <| congrArg₂ (· + ·)
          (congrArg firstCoord
            (ModuleCat.BalancedTensor.map_mk ℚ (ℚ × ℚ) (ℚ × ℚ) twoThreeQ _ _))
          (congrArg firstCoord
            (ModuleCat.BalancedTensor.map_mk ℚ (ℚ × ℚ) (ℚ × ℚ) oneFiveQ _ _))
    _ = 3 := by
        rw [firstCoord_bmk, firstCoord_bmk]
        norm_num

/-! ## The outer left module and its ground comparison

Here `ℚ × ℚ` also acts on the left of the left factor, commuting with its right action. -/

/-- The computed outer action of `s` on `Bal`. -/
abbrev lact (s : ℚ × ℚ) : Module.End ℚ Bal :=
  @TensorProduct.Balanced.leftAction ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ _ groundQ
    _ _ _ _ _ s

theorem lact_bmk (s q n : ℚ × ℚ) : lact s (bmk q n) = bmk (s * q) n :=
  @TensorProduct.Balanced.leftAction_mk ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ _ groundQ
    _ _ _ _ _ s q n

/-- `(0,1)` kills `(1,1) ⊗ (1,0)` through the balancing relation, while `(1,0)` does not. -/
example : lact ((0 : ℚ), (1 : ℚ)) (bmk ((1 : ℚ), (1 : ℚ)) ((1 : ℚ), (0 : ℚ))) = 0 := by
  rw [lact_bmk]
  have h := @TensorProduct.Balanced.balance ℚ (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ groundQ _ _
    ((0 : ℚ), (1 : ℚ)) ((0 : ℚ), (1 : ℚ)) ((1 : ℚ), (0 : ℚ))
  have h1 : (op ((0 : ℚ), (1 : ℚ)) • ((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) =
      ((0 : ℚ), (1 : ℚ)) * ((1 : ℚ), (1 : ℚ)) := by
    rw [op_smul_eq_mul]
    simp
  have h2 : (((0 : ℚ), (1 : ℚ)) • (show qq.carrier from ((1 : ℚ), (0 : ℚ))) : qq.carrier) =
      0 := by
    change ((0 : ℚ), (1 : ℚ)) * ((1 : ℚ), (0 : ℚ)) = 0
    simp
  rw [h1, h2, map_zero] at h
  exact h

example : firstCoord (lact ((1 : ℚ), (0 : ℚ)) (bmk ((1 : ℚ), (1 : ℚ)) ((1 : ℚ), (0 : ℚ)))) = 1 := by
  rw [lact_bmk, firstCoord_bmk]
  norm_num

/-- The ground scalar `2` acts through `algebraMap ℚ (ℚ × ℚ)` as the ground multiple `2`. -/
example : lact (algebraMap ℚ (ℚ × ℚ) 2) = (2 : ℚ) • (1 : Module.End ℚ Bal) :=
  @TensorProduct.Balanced.leftAction_algebraMap ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) qq.carrier _ _ _ _ _ _
    groundQ _ _ _ _ _ _ _ 2

/-- The outer-module functor on `twoThreeQ`, computed on a pure class. -/
example :
    ((ModuleCat.BalancedTensor.Left.functor ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).map twoThreeQ).hom
        (bmk ((1 : ℚ), (1 : ℚ)) ((1 : ℚ), (1 : ℚ))) =
      bmk ((1 : ℚ), (1 : ℚ)) ((2 : ℚ), (3 : ℚ)) := by
  refine (ModuleCat.BalancedTensor.Left.map_mk ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) twoThreeQ _ _).trans ?_
  congr 1
  change ((2, 3) : ℚ × ℚ) * ((1 : ℚ), (1 : ℚ)) = ((2 : ℚ), (3 : ℚ))
  norm_num

/-- A pure class viewed in the outer-module object, whose `ℚ × ℚ`-module is the computed one. -/
abbrev lbmk (q n : ℚ × ℚ) :
    (ModuleCat.BalancedTensor.Left.functor ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).obj qq :=
  bmk q n

/-- The object's scalar action is the computed outer action. -/
example (s q n : ℚ × ℚ) : s • lbmk q n = lact s (bmk q n) :=
  rfl

/-- Maps of the outer-module functor are linear for the computed action: applying `twoThreeQ`
after the scalar `(1,0)` gives `(1,0)(1,1) ⊗ (2,3)`, read as `2` by `firstCoord`. -/
example :
    firstCoord (((ModuleCat.BalancedTensor.Left.functor ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).map
        twoThreeQ).hom (((1 : ℚ), (0 : ℚ)) • lbmk ((1 : ℚ), (1 : ℚ)) ((1 : ℚ), (1 : ℚ)))) = 2 := by
  rw [LinearMap.map_smul]
  calc _ = firstCoord (lact ((1 : ℚ), (0 : ℚ))
        (bmk ((1 : ℚ), (1 : ℚ)) (((2, 3) : ℚ × ℚ) * ((1 : ℚ), (1 : ℚ))))) :=
        congrArg (fun x => firstCoord (lact ((1 : ℚ), (0 : ℚ)) x))
          (ModuleCat.BalancedTensor.Left.map_mk ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) twoThreeQ _ _)
    _ = 2 := by
        rw [lact_bmk, firstCoord_bmk]
        norm_num

example :
    (ModuleCat.BalancedTensor.Left.functor ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).map
        (twoThreeQ + oneFiveQ) =
      (ModuleCat.BalancedTensor.Left.functor ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).map twoThreeQ +
        (ModuleCat.BalancedTensor.Left.functor ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).map oneFiveQ :=
  (ModuleCat.BalancedTensor.Left.additive ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).map_add

/-- Restricting the outer module to `ℚ` recovers the ground functor by the identity on classes. -/
example :
    ((ModuleCat.BalancedTensor.Left.groundIso ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ)).app qq).hom.hom
        (bmk ((1 : ℚ), (1 : ℚ)) ((1 : ℚ), (0 : ℚ))) = bmk ((1 : ℚ), (1 : ℚ)) ((1 : ℚ), (0 : ℚ)) :=
  ModuleCat.BalancedTensor.Left.groundIso_hom_apply ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) qq _

/-! ## Extension of scalars along `ℤ → ℚ` on the rank-one `ℤ`-module -/

/-- Multiplication by `2` and by `3` on `ℤ`. -/
abbrev twoInt : intLine ⟶ intLine := ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)

abbrev threeInt : intLine ⟶ intLine := ModuleCat.ofHom ((3 : ℤ) • LinearMap.id)

example :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).map (twoInt + threeInt) =
      (ModuleCat.extendScalars (Int.castRingHom ℚ)).map twoInt +
        (ModuleCat.extendScalars (Int.castRingHom ℚ)).map threeInt :=
  (ModuleCat.extendScalars_additive (Int.castRingHom ℚ)).map_add

example :
    ((ModuleCat.extendScalars (Int.castRingHom ℚ)).map (twoInt + threeInt)).hom
        ((1 : ℚ) ⊗ₜ[ℤ,Int.castRingHom ℚ] (1 : ℤ)) =
      (1 : ℚ) ⊗ₜ[ℤ,Int.castRingHom ℚ] (5 : ℤ) := by
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

/-- The cast `ℤ → ℚ` as a map into the restriction of `ℚ`. -/
def castLine : intLine ⟶ (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj ratLine :=
  ModuleCat.ofHom (X := ℤ) (Y := (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj ratLine)
    { toFun := fun n => (show ℚ from (n : ℚ))
      map_add' := fun a b => by
        change ((a + b : ℤ) : ℚ) = (a : ℚ) + (b : ℚ)
        push_cast
        rfl
      map_smul' := fun c n => by
        change ((c * n : ℤ) : ℚ) = (Int.castRingHom ℚ c) • (n : ℚ)
        simp }

/-- Evaluation `s ⊗ n ↦ s * n` on the extension of `ℤ`, through the counit. -/
def evalQ : (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj intLine ⟶ ratLine :=
  (ModuleCat.extendScalars (Int.castRingHom ℚ)).map castLine ≫
    (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).counit.app ratLine

theorem evalQ_one_tmul (n : ℤ) :
    evalQ.hom ((1 : ℚ) ⊗ₜ[ℤ,Int.castRingHom ℚ] n) = (n : ℚ) :=
  (congrArg ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).counit.app ratLine).hom
      (ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) castLine 1 n)).trans
    (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul (Int.castRingHom ℚ) ratLine _)

/-- `evalQ` reads the extension of multiplication by `2` on `1 ⊗ 1` as `2`. -/
theorem evalQ_two :
    evalQ.hom (((ModuleCat.extendScalars (Int.castRingHom ℚ)).map twoInt).hom
      ((1 : ℚ) ⊗ₜ[ℤ,Int.castRingHom ℚ] (1 : ℤ))) = 2 :=
  ((congrArg evalQ.hom (ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) twoInt 1 1)).trans
    (evalQ_one_tmul _)).trans (by norm_num)

theorem evalQ_three :
    evalQ.hom (((ModuleCat.extendScalars (Int.castRingHom ℚ)).map threeInt).hom
      ((1 : ℚ) ⊗ₜ[ℤ,Int.castRingHom ℚ] (1 : ℤ))) = 3 :=
  ((congrArg evalQ.hom (ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) threeInt 1 1)).trans
    (evalQ_one_tmul _)).trans (by norm_num)

/-- Nonvacuity: the extended multiplications by `2` and `3` differ. -/
example :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).map twoInt ≠
      (ModuleCat.extendScalars (Int.castRingHom ℚ)).map threeInt := by
  intro h
  have h' := congrArg (fun φ => evalQ.hom (φ.hom ((1 : ℚ) ⊗ₜ[ℤ,Int.castRingHom ℚ] (1 : ℤ)))) h
  have h23 : (2 : ℚ) = 3 := evalQ_two.symm.trans (h'.trans evalQ_three)
  norm_num at h23

end MathlibExtTest.ProductRingTensorClients
