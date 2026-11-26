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
# Naturality of adjoint exterior coinvariants

Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
and f:L→L′, g:S→S′ Lie maps with fι=ι′g. Exterior powers of f
intertwine the adjoint actions. They descend to a chain map
F:Q(L,ι)→Q(L′,ι′) satisfying Fq=q′Λf and
F_n([x_1∧⋯∧x_n])=[f(x_1)∧⋯∧f(x_n)].

The descended maps preserve identities, composition, coproducts,
counits and coaugmentations. Their homology maps are H_n(F).
The L-family occupies universe v and the acting S-family universe u
of the ground ring; the chain category has height max{u,v}.
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


/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
The tensor coordinates for the coinvariant chain maps use
M⊗_R N and the lifted regular tensor unit. -/
local instance coinvariantNaturalityTensorStructure : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
These tensor coordinates satisfy the associator and unitor laws,
giving the monoidal structure for coinvariant maps. -/
local instance coinvariantNaturalityMonoidalCategory : MonoidalCategory (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
local instance coinvariantNaturalityMonoidalPreadditive : MonoidalPreadditive (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
local instance coinvariantNaturalityMonoidalLinear : MonoidalLinear R (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)

local instance coinvariantNaturalityFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)
/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
The internal R-linear Hom module is right adjoint to tensoring,
so the coefficient category is monoidal closed. -/
local instance coinvariantNaturalityClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)

/-- Let R be commutative and f:L→L′, g:S→S′ Lie homomorphisms,
with the L-family in universe v and S-family in the ring universe u.
The maps g⊗Λ_R^n f form a chain map
S⊗_R C_*(L)→S′⊗_R C_*(L′), where only the exterior factor
carries the Chevalley–Eilenberg differential. -/
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

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
Writing α,α′ for the adjoint tensor actions, the chain square is
(Λf)α=α′(g⊗Λf). -/
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

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
The exterior Lie chain map descends to an R-module chain map
F:Q→Q′ with Fq=q′Λf. -/
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

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
On projected decomposable generators,
F_n([x_1∧⋯∧x_n])=[f(x_1)∧⋯∧f(x_n)]. -/
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

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The pair of identity Lie homomorphisms on L and S induces
id_Q on the coinvariant chain complex. -/
theorem adjointCoinvariantMap_id :
    adjointCoinvariantMap R L ι ι (LieHom.id : L →ₗ⁅R⁆ L)
      (LieHom.id : S →ₗ⁅R⁆ S) (by ext s; rfl) = 𝟙 (adjointCoinvariantComplex R L ι) := by
  apply (cancel_epi (adjointCoinvariantProjection R L ι)).mp
  rw [adjointCoinvariantMap_projection, nativeComplexMap_id, Category.id_comp, Category.comp_id]

/-- Let two composable commuting diagrams of Lie maps be given,
fι=ι′g and f′ι′=ι″g′, and let the composite diagram
(f′f)ι=ι″(g′g) commute. The induced coinvariant chain maps satisfy
Q(f′,g′)Q(f,g)=Q(f′f,g′g), with R commutative and the same
two carrier universes throughout. -/
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

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
The descended chain map preserves the counits:
ε_{Q′}F=ε_Q. -/
theorem adjointCoinvariantMap_counit
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointCoinvariantMap R L ι ι' f g h ≫ adjointCoinvariantCounit R L' ι' =
      adjointCoinvariantCounit R L ι := by
  apply (cancel_epi (adjointCoinvariantProjection R L ι)).mp
  rw [← Category.assoc, adjointCoinvariantMap_projection, Category.assoc,
    adjointCoinvariantCounit_projection, nativeComplexMap_counit,
    adjointCoinvariantCounit_projection]

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
The descended chain map preserves the coproducts:
Δ_{Q′}F=(F⊗F)Δ_Q. -/
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

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
The coaugmentation square is Fu_Q=u_{Q′}. -/
theorem adjointCoinvariantMap_coaug
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    adjointCoinvariantCoaug R L ι ≫ adjointCoinvariantMap R L ι ι' f g h =
      adjointCoinvariantCoaug R L' ι' := by
  rw [adjointCoinvariantCoaug, Category.assoc, adjointCoinvariantMap_projection,
    ← Category.assoc, nativeComplexMap_coaug, adjointCoinvariantCoaug]

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
The coproduct and counit squares give F:Q→Q′ the structure
of a comonoid morphism. -/
def adjointCoinvariantMapIsComonHom
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) :
    letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
    letI : ComonObj (adjointCoinvariantComplex R L' ι') := adjointCoinvariantComonObj R L' ι'
    IsComonHom (adjointCoinvariantMap R L ι ι' f g h) := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  letI : ComonObj (adjointCoinvariantComplex R L' ι') := adjointCoinvariantComonObj R L' ι'
  exact ⟨adjointCoinvariantMap_counit R L ι ι' f g h,
    adjointCoinvariantMap_comul R L ι ι' f g h⟩

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The degree-n adjoint coinvariant homology is H_n(Q), the
homology of the quotient chain complex. -/
abbrev adjointCoinvariantHomology (n : ℕ) := (adjointCoinvariantComplex R L ι).homology n

/-- Let R be commutative, ι:S→L and ι′:S′→L′ Lie homomorphisms,
with L,L′ in universe v and S,S′ in the ring universe u.
Let f:L→L′ and g:S→S′ be R-Lie maps satisfying fι=ι′g.
Write Q,Q′ for the adjoint coinvariant complexes and q,q′ for their projections.
The induced map on degree-n coinvariant homology is
H_n(F):H_n(Q)→H_n(Q′). -/
def adjointCoinvariantHomologyMap
    (f : L →ₗ⁅R⁆ L') (g : S →ₗ⁅R⁆ S') (h : f.comp ι = ι'.comp g) (n : ℕ) :
    adjointCoinvariantHomology R L ι n ⟶ adjointCoinvariantHomology R L' ι' n :=
  HomologicalComplex.homologyMap (adjointCoinvariantMap R L ι ι' f g h) n

end ChevalleyEilenberg
