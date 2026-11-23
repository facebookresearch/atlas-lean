/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The Alexander--Whitney component formula is adapted from:
TauCeti/AlgebraicTopology/DoldKan/AlexanderWhitney.lean,
revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0.
Authors: The Tau Ceti contributors.
Modification: state the same front/back formula for the published actual
Nisnevich tensor bifunctor, whose ring and module universes differ.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicRealizationComparisons
public import MathlibExt.CategoryTheory.DGSourceMore.DoldKanMonoidal
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# External-cycle and Eilenberg--Zilber Tate products

The raw product is the external finite-cycle product followed by the
actual source diagonal and torus concatenation. Singular multiplication
is fixed on these cycle classes. Its chain map is the signed shuffle
sum, and the opposite Alexander--Whitney map has the front/back face
formula of the imported public source port. Native total complexes
retain all Koszul differentials and all tensor summands.

These source contracts specify construction maps. Quasi-isomorphism,
associativity, commutativity and motivic representability are separate
Wanted conclusions.

Sources: Mazza--Voevodsky--Weibel, Constructions 3.10--3.11, pp. 23--24;
Voevodsky arXiv:math/0107109v1, Section 2, pp. 3--5.
The Alexander--Whitney and Dold--Kan port imports retain Tau Ceti revision
62bbc0596dc3539d488232e4e924a338548ea0a9, Apache 2.0 and author credits.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicCycleProducts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicEilenbergMacLaneModels
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- The literal product diagonal in the chosen native fibre product. -/
def smoothDiagonal (P : SmoothProductSystem k) (U : SmoothScheme k) :
    U ⟶ P.obj U U :=
  Over.homMk
    (pullback.lift (𝟙 U.scheme.left) (𝟙 U.scheme.left) (by simp) ≫
      (P.geometry U U).iso.inv) (by
    dsimp only [SmoothProductSystem.obj, productScheme] at *
    rw [← (P.geometry U U).base_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      pullback.lift_fst_assoc, Category.id_comp])

/-- Torus concatenation is fixed by both exponent-coordinate inclusions,
including the whole native product scheme isomorphism. -/
structure TorusConcatenation {P : SmoothProductSystem k}
    (A : StandardSchemes P) where
  firstRing : ∀ q r : ℕ, torusRing k q →ₐ[k] torusRing k (q + r)
  first_monomial : ∀ (q r : ℕ) (v : Fin q → ℤ) (a : k),
    firstRing q r (AddMonoidAlgebra.single v a) =
      AddMonoidAlgebra.single (Fin.append v (fun _ : Fin r => 0)) a
  secondRing : ∀ q r : ℕ, torusRing k r →ₐ[k] torusRing k (q + r)
  second_monomial : ∀ (q r : ℕ) (v : Fin r → ℤ) (a : k),
    secondRing q r (AddMonoidAlgebra.single v a) =
      AddMonoidAlgebra.single (Fin.append (fun _ : Fin q => 0) v) a
  iso : ∀ q r : ℕ, P.obj (A.torus q) (A.torus r) ≅ A.torus (q + r)
  first_coordinate : ∀ q r : ℕ,
    (iso q r).inv.left ≫ (P.geometry (A.torus q) (A.torus r)).fst.left =
      (A.torusIso (q + r)).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (firstRing q r).toRingHom) ≫
            (A.torusIso q).inv
  second_coordinate : ∀ q r : ℕ,
    (iso q r).inv.left ≫ (P.geometry (A.torus q) (A.torus r)).snd.left =
      (A.torusIso (q + r)).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (secondRing q r).toRingHom) ≫
            (A.torusIso r).inv

/-- An `(a,b)` shuffle with the two internally increasing blocks. -/
def Shuffle (a b : ℕ) := {s : Equiv.Perm (Fin (a + b)) //
  StrictMono (fun i : Fin a => s (Fin.castAdd b i)) ∧
  StrictMono (fun j : Fin b => s (Fin.natAdd a j))}

instance (a b : ℕ) : Finite (Shuffle a b) := by
  unfold Shuffle
  infer_instance

/-- First shuffle surjection: count first-block steps before this vertex. -/
def shuffleFirst {a b : ℕ} (s : Shuffle a b) : ⦋a + b⦌ ⟶ ⦋a⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨(Finset.univ.filter fun j : Fin a =>
        (s.val (Fin.castAdd b j)).val < i.val).card, by
        have h := Finset.card_le_card (Finset.filter_subset
          (fun j : Fin a => (s.val (Fin.castAdd b j)).val < i.val)
            Finset.univ)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        omega⟩
      monotone' := by
        intro i j hij
        change (Finset.univ.filter (fun x : Fin a =>
          (s.val (Fin.castAdd b x)).val < i.val)).card ≤
          (Finset.univ.filter (fun x : Fin a =>
            (s.val (Fin.castAdd b x)).val < j.val)).card
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact lt_of_lt_of_le hx hij }

/-- Second shuffle surjection: count second-block steps before this vertex. -/
def shuffleSecond {a b : ℕ} (s : Shuffle a b) : ⦋a + b⦌ ⟶ ⦋b⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨(Finset.univ.filter fun j : Fin b =>
        (s.val (Fin.natAdd a j)).val < i.val).card, by
        have h := Finset.card_le_card (Finset.filter_subset
          (fun j : Fin b => (s.val (Fin.natAdd a j)).val < i.val)
            Finset.univ)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        omega⟩
      monotone' := by
        intro i j hij
        change (Finset.univ.filter (fun x : Fin b =>
          (s.val (Fin.natAdd a x)).val < i.val)).card ≤
          (Finset.univ.filter (fun x : Fin b =>
            (s.val (Fin.natAdd a x)).val < j.val)).card
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact lt_of_lt_of_le hx hij }

/-- The literal degreewise sheaf tensor bifunctor. -/
def simplicialTensor (N : NisTensorSystem k)
    (F H : SimplicialObject (NisModules (k := k))) :
    SimplicialObject (NisModules (k := k)) where
  obj n := (N.functor.obj (F.obj n)).obj (H.obj n)
  map {n m} a := (N.functor.map (F.map a)).app (H.obj n) ≫
    (N.functor.obj (F.obj m)).map (H.map a)
  map_id n := by simp
  map_comp {n m t} a b := by
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [NatTrans.naturality_assoc]

/-- The signed Eilenberg--Zilber summand sum on actual simplex maps. -/
def shuffleComponent (N : NisTensorSystem k)
    (F H : SimplicialObject (NisModules (k := k))) (a b : ℕ) :
    (N.functor.obj (F.obj (op ⦋a⦌))).obj (H.obj (op ⦋b⦌)) ⟶
      (simplicialTensor N F H).obj (op ⦋a + b⦌) := by
  classical
  letI := Fintype.ofFinite (Shuffle a b)
  exact ∑ s : Shuffle a b, ((Equiv.Perm.sign s.val : ℤˣ) : ℤ) •
    ((N.functor.map (F.map (shuffleFirst s).op)).app (H.obj (op ⦋b⦌)) ≫
      (N.functor.obj (F.obj (op ⦋a + b⦌))).map
        (H.map (shuffleSecond s).op))

variable (N : NisTensorSystem k)
  [N.functor.PreservesZeroMorphisms]
  [∀ F, (N.functor.obj F).PreservesZeroMorphisms]

/-- Native small tensor totalizations exist by sheafified module coproducts. -/
theorem tensor_total_exists {I₁ I₂ J : Type} {c₁ : ComplexShape I₁}
    {c₂ : ComplexShape I₂} (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
    (F : HomologicalComplex (NisModules (k := k)) c₁)
    (H : HomologicalComplex (NisModules (k := k)) c₂) :
    HomologicalComplex.HasMapBifunctor F H N.functor c :=
  fun j => by
    let h : HasColimitsOfShape
        (Discrete ((ComplexShape.π c₁ c₂ c) ⁻¹' {j}))
        (NisModules (k := k)) := by
      exact (inferInstance : HasColimitsOfSize.{0, 0}
        (NisModules (k := k))).has_colimits_of_shape _
    exact h.has_colimit _

/-- Native integer-cochain tensor totalizations. -/
instance cochainTensorTotal
    (F H : CochainComplex (NisModules (k := k)) ℤ) :
    HomologicalComplex.HasMapBifunctor F H N.functor (ComplexShape.up ℤ) :=
  tensor_total_exists N (ComplexShape.up ℤ) F H

/-- Native nonnegative-chain tensor totalizations. -/
instance chainTensorTotal
    (F H : ChainComplex (NisModules (k := k)) ℕ) :
    HomologicalComplex.HasMapBifunctor F H N.functor (ComplexShape.down ℕ) :=
  tensor_total_exists N (ComplexShape.down ℕ) F H

/-- The actual tensor total complex, with the native Koszul differential. -/
abbrev cochainTensor (F H : CochainComplex (NisModules (k := k)) ℤ) :=
  HomologicalComplex.mapBifunctor F H N.functor (ComplexShape.up ℤ)

/-- Native nonnegative tensor total complex. -/
abbrev chainTensor (F H : ChainComplex (NisModules (k := k)) ℕ) :=
  HomologicalComplex.mapBifunctor F H N.functor (ComplexShape.down ℕ)

/-- Native alternating-face chains, with their coefficient category explicit. -/
abbrev alternatingChains (F : SimplicialObject (NisModules (k := k))) :
    ChainComplex (NisModules (k := k)) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (NisModules (k := k))).obj F

/-- The exact front/back Alexander--Whitney component of the source port. -/
def alexanderWhitneyComponent
    (F H : SimplicialObject (NisModules (k := k))) (n : ℕ) :
    (simplicialTensor N F H).obj (op ⦋n⦌) ⟶
      (chainTensor N (alternatingChains F) (alternatingChains H)).X n :=
  ∑ a : Fin (n + 1),
    ((N.functor.map
      (F.map (SimplexCategory.subinterval 0 a.val (by omega)).op)).app
        (H.obj (op ⦋n⦌)) ≫
      (N.functor.obj (F.obj (op ⦋a.val⦌))).map
        (H.map (SimplexCategory.subinterval a.val (n - a.val) (by omega)).op)) ≫
      HomologicalComplex.ιMapBifunctor
        (alternatingChains F) (alternatingChains H)
        N.functor (ComplexShape.down ℕ) a.val (n - a.val) n (by dsimp; omega)

/-- The summand formula fixing a shuffle chain map: on the `(a, b)` summand it is the sum
of the signed shuffle components. -/
def IsShuffleNormalized
    (shuffle : ∀ F H : SimplicialObject (NisModules (k := k)),
      chainTensor N (alternatingChains F) (alternatingChains H) ⟶
        alternatingChains (simplicialTensor N F H)) : Prop :=
  ∀ (F H : SimplicialObject (NisModules (k := k))) (a b : ℕ),
    HomologicalComplex.ιMapBifunctor
      (alternatingChains F) (alternatingChains H)
      N.functor (ComplexShape.down ℕ) a b (a + b) rfl ≫
        (shuffle F H).f (a + b) = shuffleComponent N F H a b

/-- Shuffle and Alexander--Whitney chain maps, fully fixed by their
native summand formulas. Neither inverse nor quasi-isomorphism is assumed. -/
structure EilenbergZilberModel where
  shuffle : ∀ F H : SimplicialObject (NisModules (k := k)),
    chainTensor N (alternatingChains F) (alternatingChains H) ⟶
      alternatingChains (simplicialTensor N F H)
  shuffle_summand : IsShuffleNormalized N shuffle
  alexanderWhitney : ∀ F H : SimplicialObject (NisModules (k := k)),
    alternatingChains (simplicialTensor N F H) ⟶
      chainTensor N (alternatingChains F) (alternatingChains H)
  alexanderWhitney_component : ∀ (F H : SimplicialObject (NisModules (k := k))) (n : ℕ),
    (alexanderWhitney F H).f n = alexanderWhitneyComponent N F H n

/-- A pure tensor's actual image through the native sheafification unit. -/
def tensorElement (F H : NisModules (k := k)) (U : (SmoothScheme k)ᵒᵖ)
    (x : F.obj.obj U) (y : H.obj.obj U) :
    ((N.functor.obj F).obj H).obj.obj U :=
  ((N.objectIso F H).inv.hom.app U)
    ((((sheafificationAdjunction (nisnevichTopology (k := k))
      (ModuleCat.{1} ℤ)).unit.app (N.presheaf F H)).app U)
        ((N.termIso F H U).inv (TensorProduct.tmul ℤ x y)))

/-- A coefficient element enters the actual constant sheaf by its unit. -/
def constantElement (V : ModuleCat.{1} ℤ) (U : (SmoothScheme k)ᵒᵖ) (v : V) :
    (constantCoefficient (k := k) V).obj.obj U :=
  (((sheafificationAdjunction (nisnevichTopology (k := k))
    (ModuleCat.{1} ℤ)).unit.app
      ((Functor.const (SmoothScheme k)ᵒᵖ).obj V)).app U) v

variable {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R))

/-- The actual projection onto the reduced torus cokernel. -/
def torusProjection (q : ℕ) :
    (R.functor.obj ⟨A.torus q⟩).obj ⟶
      reducedTorusPresheaf (D := D) (G := G) (P := P) (A := A) (R := R) q
    := match q with
  | 0 => 𝟙 _
  | q + 1 => cokernel.π (Sigma.desc (fun i : Fin (q + 1) =>
      (R.functor.map (show (⟨A.torus q⟩ : CorrespondenceObject D G) ⟶
        ⟨A.torus (q + 1)⟩ from graphCycle G (A.unitInsertion q i))).hom))

/-- A finite cycle enters the fixed reduced torus quotient. -/
def torusClass (q : ℕ) (U : SmoothScheme k) (z : Cycles U (A.torus q)) :
    ((T.reduced q).object.obj).obj (op ⟨U⟩) :=
  ((T.reduced q).iso.inv.app (op ⟨U⟩))
    ((torusProjection (D := D) (G := G) (P := P) (A := A) (R := R) q).app
      (op ⟨U⟩)
      (((eqToHom (R.object_eq ⟨A.torus q⟩)).hom.app (op ⟨U⟩))
        (((R.model ⟨A.torus q⟩).valueIso ⟨U⟩).inv (ULift.up z))))

/-- A singular cycle class, using the exact simplex product and transfer
sheafification unit of the published source models. -/
def singularClass (q : ℕ) (n : SimplexCategoryᵒᵖ) (U : SmoothScheme k)
    (z : Cycles (P.obj (A.simplex.obj n.unop) U) (A.torus q)) :
    ((singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T q).obj n).obj.obj (op U) :=
  (((S.adjunction.unit.app ((T.singular q).object.obj n)).hom.app (op ⟨U⟩)))
    (((T.singular q).degreeIso n).inv.app (op ⟨U⟩)
      (((T.reduced q).object.obj.map
        (eqToHom (C.objects_eq ⟨A.simplex.obj n.unop⟩ ⟨U⟩)).op)
          (torusClass T q (P.obj (A.simplex.obj n.unop) U) z)))

/-- The source product of two finite cycles on the same smooth base. -/
def diagonalCycleProduct (J : TorusConcatenation A) (q r : ℕ)
    (U : SmoothScheme k) (z : Cycles U (A.torus q))
    (w : Cycles U (A.torus r)) : Cycles U (A.torus (q + r)) :=
  composeCycles D (graphCycle G (smoothDiagonal P U))
    (composeCycles D (externalCycles E z w) (graphCycle G (J.iso q r).hom))

/-- The cycle formula fixing a singular multiplication: on the classes of two finite cycles
it is the class of their external product pulled back along the diagonal and concatenated. -/
def IsCyclePairingNormalized (J : TorusConcatenation A)
    (pairing : ∀ q r : ℕ,
      simplicialTensor N
        (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
          (A := A) (R := R) (S := S) T q)
        (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
          (A := A) (R := R) (S := S) T r) ⟶
        singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
          (A := A) (R := R) (S := S) T (q + r)) : Prop :=
  ∀ (q r : ℕ) (n : SimplexCategoryᵒᵖ) (U : SmoothScheme k)
    (z : Cycles (P.obj (A.simplex.obj n.unop) U) (A.torus q))
    (w : Cycles (P.obj (A.simplex.obj n.unop) U) (A.torus r)),
    (((pairing q r).app n).hom.app (op U))
      (tensorElement N _ _ (op U) (singularClass T q n U z)
        (singularClass T r n U w)) =
      singularClass T (q + r) n U
        (diagonalCycleProduct (D := D) (G := G) (E := E)
          J q r (P.obj (A.simplex.obj n.unop) U) z w)

/-- Singular multiplication is fixed on every pair of literal finite
cycle classes by external product, diagonal pullback and concatenation. -/
structure SingularCycleProduct (J : TorusConcatenation A) where
  pairing : ∀ q r : ℕ,
    simplicialTensor N
      (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
        (A := A) (R := R) (S := S) T q)
      (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
        (A := A) (R := R) (S := S) T r) ⟶
      singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
        (A := A) (R := R) (S := S) T (q + r)
  cycle_pairing : IsCyclePairingNormalized N T J pairing

/-- The unshifted Tate multiplication is precisely shuffle then the
alternating-face map of the external-cycle singular multiplication. -/
def unshiftedMultiplication {J : TorusConcatenation A}
    (M : SingularCycleProduct N T J) (Z : EilenbergZilberModel N) (q r : ℕ) :=
  Z.shuffle
    (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T q)
    (singularNis (D := D) (G := G) (P := P) (E := E) (C := C)
      (A := A) (R := R) (S := S) T r) ≫
    (AlgebraicTopology.alternatingFaceMapComplex _).map (M.pairing q r)

end MathlibExt.AlgebraicGeometry.MotivicCycleProducts
