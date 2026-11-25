/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.AdjointCoinvariantCoalgebra
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNaturality
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Naturality of adjoint Chevalley–Eilenberg coinvariants

A commuting square of Lie algebra maps intertwines the adjoint actions, so
the induced Chevalley–Eilenberg chain map descends to coinvariants. Its
components preserve projected wedges, identities, compositions, coproducts,
counits, and coaugmentations. Homology maps are induced by these chain maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type u} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)
variable {L' L'' : Type v} [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
variable {S' S'' : Type u} [LieRing S'] [LieAlgebra R S'] [LieRing S''] [LieAlgebra R S'']
variable (ι' : S' →ₗ⁅R⁆ L')


/-- The fixed canonical tensor data for the natural coinvariant maps. -/
local instance coinvariantNaturalityTensorStructure : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
/-- The canonical monoidal laws used in coinvariant naturality. -/
local instance coinvariantNaturalityMonoidalCategory : MonoidalCategory (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
local instance coinvariantNaturalityMonoidalPreadditive : MonoidalPreadditive (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
local instance coinvariantNaturalityMonoidalLinear : MonoidalLinear R (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)

local instance coinvariantNaturalityFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)
/-- Closedness of the original coefficient tensor product. -/
local instance coinvariantNaturalityClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)

/-- Lie maps act on the scalar tensor complexes through their tensor maps. -/
def adjointActionComplexMap (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') :
    adjointActionComplex R L (S := S) ⟶ adjointActionComplex R L' (S := S') :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (TensorProduct.map g.toLinearMap (exteriorPower.map n f.toLinearMap)))
    (fun n => by
      rw [adjointActionComplex_d_succ, adjointActionComplex_d_succ]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s a
      change g s ⊗ₜ[R] differential R L' n (exteriorPower.map (n + 1) f.toLinearMap a) =
        g s ⊗ₜ[R] exteriorPower.map n f.toLinearMap (differential R L n a)
      exact congrArg (fun b => g s ⊗ₜ[R] b)
        (LinearMap.congr_fun (differential_naturality R L f n) a))

/-- The commuting Lie square gives the scalar-action chain square. -/
theorem adjointActionChainMap_naturality
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointActionChainMap R L ι ≫ nativeComplexMap R L f =
      adjointActionComplexMap R L f g ≫ adjointActionChainMap R L' ι' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  have hι : f (ι s) = ι' (g s) := congrArg (fun t => t s) h
  have ha := LinearMap.congr_fun (degreeAdjointAction_naturality R L f n (ι s)) a
  change exteriorPower.map n f.toLinearMap (degreeAdjointAction R L n (ι s) a) =
    degreeAdjointAction R L' n (ι' (g s)) (exteriorPower.map n f.toLinearMap a)
  exact ha.trans (congrArg (fun x => degreeAdjointAction R L' n x
    (exteriorPower.map n f.toLinearMap a)) hι)

private theorem adjointCoinvariantMap_condition
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointActionChainMap R L ι ≫ (nativeComplexMap R L f ≫ (adjointCoinvariantProjection R L' ι')) = 0 := by
  rw [← Category.assoc, adjointActionChainMap_naturality R L ι ι' f g h, Category.assoc]
  unfold adjointCoinvariantProjection
  exact (congrArg (fun t => adjointActionComplexMap R L f g ≫ t)
    (cokernel.condition (adjointActionChainMap R L' ι'))).trans comp_zero

/-- The CE Lie map descends to the native coinvariant cokernel. -/
def adjointCoinvariantMap (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    (adjointCoinvariantComplex R L ι) ⟶ (adjointCoinvariantComplex R L' ι') :=
  cokernel.desc (adjointActionChainMap R L ι) (nativeComplexMap R L f ≫ (adjointCoinvariantProjection R L' ι'))
    (by
      rw [← Category.assoc, adjointActionChainMap_naturality R L ι ι' f g h, Category.assoc]
      unfold adjointCoinvariantProjection
      exact (congrArg (fun t => adjointActionComplexMap R L f g ≫ t)
        (cokernel.condition (adjointActionChainMap R L' ι'))).trans comp_zero)

@[reassoc]
theorem adjointCoinvariantMap_projection
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    (adjointCoinvariantProjection R L ι) ≫ adjointCoinvariantMap R L ι ι' f g h = nativeComplexMap R L f ≫
      (adjointCoinvariantProjection R L' ι') :=
  cokernel.π_desc _ _ _

/-- The induced coinvariant map keeps the pure-wedge formula on projected generators. -/
theorem adjointCoinvariantMap_pure
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g)
    (n : ℕ) (v : Fin n → L) :
    ((adjointCoinvariantMap R L ι ι' f g h).f n).hom
        (((adjointCoinvariantProjection R L ι).f n).hom (exteriorPower.ιMulti R n v)) =
      ((adjointCoinvariantProjection R L' ι').f n).hom (exteriorPower.ιMulti R n (f ∘ v)) := by
  have hp := congrArg (fun t => (t.f n).hom (exteriorPower.ιMulti R n v))
    (adjointCoinvariantMap_projection R L ι ι' f g h)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  exact hp.trans (congrArg ((adjointCoinvariantProjection R L' ι').f n).hom
    (nativeComplexMap_f_ιMulti R L f n v))

/-- Native coinvariant identity maps are the identities. -/
theorem adjointCoinvariantMap_id :
    adjointCoinvariantMap R L ι ι (LieHom.id : L →ₗ⁅R⁆ L)
      (LieHom.id : S →ₗ⁅R⁆ S) (by ext s; rfl) = 𝟙 (adjointCoinvariantComplex R L ι) := by
  apply (cancel_epi (adjointCoinvariantProjection R L ι)).mp
  rw [adjointCoinvariantMap_projection, nativeComplexMap_id, Category.id_comp, Category.comp_id]

/-- Native coinvariant maps compose from their CE maps. -/
theorem adjointCoinvariantMap_comp (ι'' : S'' →ₗ⁅R⁆ L'')
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g)
    (f' : L' →ₗ⁅R⁆ L'') (g' : S' →ₗ⁅R⁆ S'') (h' : f'.comp ι' = ι''.comp g')
    (hc : (f'.comp f).comp ι = ι''.comp (g'.comp g)) :
    adjointCoinvariantMap R L ι ι' f g h ≫ adjointCoinvariantMap R L' ι' ι'' f' g' h' =
      adjointCoinvariantMap R L ι ι'' (f'.comp f) (g'.comp g) hc := by
  apply (cancel_epi (adjointCoinvariantProjection R L ι)).mp
  rw [← Category.assoc, adjointCoinvariantMap_projection, Category.assoc,
    adjointCoinvariantMap_projection, ← Category.assoc, nativeComplexMap_comp,
    adjointCoinvariantMap_projection]

/-- The induced coinvariant map preserves the counits. -/
theorem adjointCoinvariantMap_counit
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointCoinvariantMap R L ι ι' f g h ≫ adjointCoinvariantCounit R L' ι' =
      adjointCoinvariantCounit R L ι := by
  apply (cancel_epi (adjointCoinvariantProjection R L ι)).mp
  rw [← Category.assoc, adjointCoinvariantMap_projection, Category.assoc,
    adjointCoinvariantCounit_projection, nativeComplexMap_counit,
    adjointCoinvariantCounit_projection]

/-- The induced coinvariant map preserves the coproducts. -/
theorem adjointCoinvariantMap_comul
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointCoinvariantMap R L ι ι' f g h ≫ adjointCoinvariantComul R L' ι' =
      adjointCoinvariantComul R L ι ≫ HomologicalComplex.tensorHom
        (adjointCoinvariantMap R L ι ι' f g h) (adjointCoinvariantMap R L ι ι' f g h) := by
  let K := (canonicalChainData R L).complex
  let K' := (canonicalChainData R L').complex
  let Q := adjointCoinvariantComplex R L ι
  let Q' := adjointCoinvariantComplex R L' ι'
  let q : K ⟶ Q := adjointCoinvariantProjection R L ι
  let q' : K' ⟶ Q' := adjointCoinvariantProjection R L' ι'
  let F : K ⟶ K' := nativeComplexMap R L f
  let m : Q ⟶ Q' := adjointCoinvariantMap R L ι ι' f g h
  let deltaSource : K ⟶ K ⊗ K := nativeComplexComul R L
  let deltaTarget : K' ⟶ K' ⊗ K' := nativeComplexComul R L'
  let d : Q ⟶ Q ⊗ Q := adjointCoinvariantComul R L ι
  let d' : Q' ⟶ Q' ⊗ Q' := adjointCoinvariantComul R L' ι'
  have hm : q ≫ m = F ≫ q' := adjointCoinvariantMap_projection R L ι ι' f g h
  have hd : q ≫ d = deltaSource ≫ HomologicalComplex.tensorHom q q := adjointCoinvariantComul_projection R L ι
  have hd' : q' ≫ d' = deltaTarget ≫ HomologicalComplex.tensorHom q' q' :=
    adjointCoinvariantComul_projection R L' ι'
  have hF : F ≫ deltaTarget = deltaSource ≫ HomologicalComplex.tensorHom F F := nativeComplexMap_comul R L f
  have ht₁ := HomologicalComplex.tensorHom_comp_tensorHom F q' F q'
  have ht₂ := HomologicalComplex.tensorHom_comp_tensorHom q m q m
  have ht : HomologicalComplex.tensorHom (F ≫ q') (F ≫ q') =
      HomologicalComplex.tensorHom (q ≫ m) (q ≫ m) :=
    congrArg (fun z : K ⟶ Q' => HomologicalComplex.tensorHom z z) hm.symm
  apply (cancel_epi q).1
  calc
    q ≫ (m ≫ d') = (q ≫ m) ≫ d' := (Category.assoc q m d').symm
    _ = (F ≫ q') ≫ d' := congrArg (fun z => z ≫ d') hm
    _ = F ≫ (q' ≫ d') := Category.assoc F q' d'
    _ = F ≫ (deltaTarget ≫ HomologicalComplex.tensorHom q' q') := congrArg (fun z => F ≫ z) hd'
    _ = (F ≫ deltaTarget) ≫ HomologicalComplex.tensorHom q' q' := (Category.assoc _ _ _).symm
    _ = (deltaSource ≫ HomologicalComplex.tensorHom F F) ≫ HomologicalComplex.tensorHom q' q' :=
      congrArg (fun z => z ≫ HomologicalComplex.tensorHom q' q') hF
    _ = deltaSource ≫ HomologicalComplex.tensorHom (F ≫ q') (F ≫ q') :=
      (Category.assoc _ _ _).trans (congrArg (fun z => deltaSource ≫ z) ht₁)
    _ = deltaSource ≫ HomologicalComplex.tensorHom (q ≫ m) (q ≫ m) := congrArg (fun z => deltaSource ≫ z) ht
    _ = (deltaSource ≫ HomologicalComplex.tensorHom q q) ≫ HomologicalComplex.tensorHom m m :=
      (congrArg (fun z => deltaSource ≫ z) ht₂.symm).trans (Category.assoc _ _ _).symm
    _ = (q ≫ d) ≫ HomologicalComplex.tensorHom m m :=
      congrArg (fun z => z ≫ HomologicalComplex.tensorHom m m) hd.symm
    _ = q ≫ (d ≫ HomologicalComplex.tensorHom m m) := Category.assoc _ _ _

/-- The induced coinvariant map preserves the coaugmentation. -/
theorem adjointCoinvariantMap_coaug
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointCoinvariantCoaug R L ι ≫ adjointCoinvariantMap R L ι ι' f g h =
      adjointCoinvariantCoaug R L' ι' := by
  rw [adjointCoinvariantCoaug, Category.assoc, adjointCoinvariantMap_projection,
    ← Category.assoc, nativeComplexMap_coaug, adjointCoinvariantCoaug]

/-- The native coinvariant map is an comonoid homomorphism. -/
def adjointCoinvariantMapIsComonHom
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
    letI : ComonObj (adjointCoinvariantComplex R L' ι') := adjointCoinvariantComonObj R L' ι'
    IsComonHom (adjointCoinvariantMap R L ι ι' f g h) := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  letI : ComonObj (adjointCoinvariantComplex R L' ι') := adjointCoinvariantComonObj R L' ι'
  exact ⟨adjointCoinvariantMap_counit R L ι ι' f g h,
    adjointCoinvariantMap_comul R L ι ι' f g h⟩

/-- Native homology is the accessor of the coinvariant complex. -/
abbrev adjointCoinvariantHomology (n : ℕ) := (adjointCoinvariantComplex R L ι).homology n

/-- Its induced native homology map is the accessor of the chain map. -/
def adjointCoinvariantHomologyMap
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) (n : ℕ) :
    adjointCoinvariantHomology R L ι n ⟶ adjointCoinvariantHomology R L' ι' n :=
  HomologicalComplex.homologyMap (adjointCoinvariantMap R L ι ι' f g h) n

end ChevalleyEilenberg
