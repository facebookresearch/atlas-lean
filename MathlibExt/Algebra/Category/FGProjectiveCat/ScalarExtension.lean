/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.UniverseEquivalence
public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLift
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorLeft
public import Mathlib.CategoryTheory.NatIso
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.Actions
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Scalar extension along an arbitrary associative ring homomorphism

The carrier is the actual integral balanced quotient `S ⊗_R P`. The left
`S`-action is earned from multiplication in `S`, and the right `R`-action on
`S` is multiplication by `f r`. No commutativity or centrality of `f` is used.

For a finite projective `P`, the stock finite-free retraction produces actual
finite coordinate and reconstruction maps. Their balanced extensions still
split, so the output is finite projective without a flatness assumption.
The full-subcategory functor therefore preserves the split exact structure.
Canonical shrinking and module/category lifts retain independent universes.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct ZeroObject

universe uR uS uP uQ uMR uMS uOR uHR uOS uHS

namespace ModuleCat.RingHomScalarExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual right action `s · r = s * f r`, with its associative module laws. -/
abbrev rightModule (f : R →+* S) : Module Rᵐᵒᵖ S :=
  Module.compHom (R := Sᵐᵒᵖ) S (RingHom.op f)

private theorem rightModule_smul_computation (f : R →+* S) (r : R) (s : S) :
    letI := rightModule f
    (op r) • s = s * f r := by
  let := rightModule f
  change s * (RingHom.op f (op r)).unop = s * f r
  rfl

/-- The right action uses the same original ring homomorphism on every scalar. -/
theorem rightModule_smul (f : R →+* S) (r : R) (s : S) :
    letI := rightModule f
    (op r) • s = s * f r :=
  rightModule_smul_computation f r s

/-- Left `S` multiplication commutes with the actual right `R` action. -/
theorem leftRightComm (f : R →+* S) :
    letI := rightModule f
    SMulCommClass S Rᵐᵒᵖ S := by
  let := rightModule f
  refine ⟨fun s r x => ?_⟩
  change s * (r • x) = r • (s * x)
  rw [← MulOpposite.op_unop r, rightModule_smul, rightModule_smul]
  exact (mul_assoc s x (f r.unop)).symm

/-- The actual integral quotient by the relations `s f(r) ⊗ p = s ⊗ r p`. -/
abbrev tensor (f : R →+* S) (P : Type uP) [AddCommGroup P] [Module R P] :
    Type (max uS uP) :=
  letI := rightModule f
  TensorProduct.Balanced ℤ R S P

/-- The outer `S`-module structure on the same balanced quotient. -/
instance tensorModule (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] : Module S (tensor f P) := by
  letI := rightModule f
  letI := leftRightComm f
  exact TensorProduct.Balanced.leftModule ℤ R S S P

/-- The original balanced pure representative. -/
@[expose] def pure (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] : S →ₗ[ℤ] P →ₗ[ℤ] tensor f P :=
  letI := rightModule f
  TensorProduct.Balanced.mk ℤ R S P

/-- The public pure class is the actual balanced quotient's canonical map. -/
theorem pure_eq_mk (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (s : S) (p : P) :
    pure f P s p =
      (letI := rightModule f
       TensorProduct.Balanced.mk ℤ R S P s p) :=
  rfl

/-- The defining balanced relation in the actual extension carrier. -/
theorem pure_balance (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (r : R) (s : S) (p : P) :
    pure f P (s * f r) p = pure f P s (r • p) := by
  let := rightModule f
  have h := TensorProduct.Balanced.balance ℤ R S P r s p
  rw [rightModule_smul f r s] at h
  exact h

/-- Scalar extension retains the outer multiplication on each pure class. -/
theorem smul_pure (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] (a s : S) (p : P) :
    a • pure f P s p = pure f P (a * s) p := by
  let := rightModule f
  let := leftRightComm f
  exact TensorProduct.Balanced.leftModule_smul_mk ℤ R S S P a s p

/-- The same quotient map induced by an original `R`-linear map. -/
@[expose] def linearMap (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) :
    tensor f P →ₗ[S] tensor f Q := by
  letI := rightModule f
  letI := leftRightComm f
  let g₀ : P →ₗ[ℤ] Q := g.toAddMonoidHom.toIntLinearMap
  exact TensorProduct.Balanced.mapLeft
    (k := ℤ) (R := R) (S := S) (Q := S) (Q' := S)
    (N := P) (N' := Q) (LinearMap.id : S →ₗ[ℤ] S) g₀
    (fun _ _ => rfl) (fun r p => g.map_smul r p) (fun _ _ => rfl)

/-- Scalar extension sends `s ⊗ p` to `s ⊗ g p` for the same original map. -/
theorem linearMap_pure (f : R →+* S)
    {P : Type uP} {Q : Type uQ} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) (s : S) (p : P) :
    linearMap f g (pure f P s p) = pure f Q s (g p) := by
  let := rightModule f
  let := leftRightComm f
  exact TensorProduct.Balanced.mapLeft_mk
    (k := ℤ) (R := R) (S := S) (Q := S) (Q' := S)
    (N := P) (N' := Q) (LinearMap.id : S →ₗ[ℤ] S)
    g.toAddMonoidHom.toIntLinearMap
    (fun _ _ => rfl) (fun r p => g.map_smul r p) (fun _ _ => rfl) s p

/-- Original pure representatives determine every `S`-linear map from the quotient. -/
theorem linearMap_ext (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] {Q : Type uQ} [AddCommGroup Q] [Module S Q]
    {a b : tensor f P →ₗ[S] Q}
    (h : ∀ s p, a (pure f P s p) = b (pure f P s p)) : a = b := by
  let := rightModule f
  apply LinearMap.toAddMonoidHom_injective
  exact TensorProduct.Balanced.addHom_ext ℤ R S P h

/-- Scalar extension sends the original identity linear map to the identity. -/
theorem linearMap_id (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] :
    linearMap f (LinearMap.id : P →ₗ[R] P) = LinearMap.id := by
  apply linearMap_ext f P
  intro s p
  exact linearMap_pure f (LinearMap.id : P →ₗ[R] P) s p

/-- The actual quotient maps compose on every original pure class. -/
theorem linearMap_comp (f : R →+* S) {P : Type uP} {Q : Type uQ} {U : Type uMR}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup U] [Module R U] (g : P →ₗ[R] Q) (h : Q →ₗ[R] U) :
    linearMap f (h.comp g) = (linearMap f h).comp (linearMap f g) := by
  apply linearMap_ext f P
  intro s p
  simp only [linearMap_pure, LinearMap.comp_apply]

/-- The balanced quotient, bundled as its earned left `S` module. -/
abbrev obj (f : R →+* S) (P : ModuleCat.{uP} R) :
    ModuleCat.{max uS uP} S :=
  ModuleCat.of S (tensor f P)

private abbrev genericFunctor (f : R →+* S) :
    ModuleCat.{uP} R ⥤ ModuleCat.{max uS uP} S :=
  letI := rightModule f
  letI := leftRightComm f
  ModuleCat.BalancedTensor.Left.functor ℤ R S S

private theorem genericObj_eq (f : R →+* S) (P : ModuleCat.{uP} R) :
    (genericFunctor f).obj P = obj f P := by
  let := rightModule f
  let := leftRightComm f
  have hP : Module.compHom P.carrier (algebraMap ℤ R) =
      (inferInstance : Module ℤ P.carrier) := Subsingleton.elim _ _
  dsimp only [genericFunctor, ModuleCat.BalancedTensor.Left.functor,
    ModuleCat.BalancedTensor.Left.obj, obj, tensor, tensorModule]
  rw [hP]

private def genericObjIso (f : R →+* S) (P : ModuleCat.{uP} R) :
    (genericFunctor f).obj P ≅ obj f P :=
  eqToIso (genericObj_eq f P)

private def intDictionaryObject (f : R →+* S) (P : ModuleCat.{uP} R)
    (d : Module ℤ P.carrier) : ModuleCat.{max uS uP} S :=
  letI := rightModule f
  letI := leftRightComm f
  letI : Module ℤ P.carrier := d
  letI : Module S (TensorProduct.Balanced ℤ R S P.carrier) :=
    TensorProduct.Balanced.leftModule ℤ R S S P.carrier
  ModuleCat.of S (TensorProduct.Balanced ℤ R S P.carrier)

private def intDictionaryPure (f : R →+* S) (P : ModuleCat.{uP} R)
    (d : Module ℤ P.carrier) (s : S) (p : P) : intDictionaryObject f P d :=
  letI := rightModule f
  letI := leftRightComm f
  letI : Module ℤ P.carrier := d
  TensorProduct.Balanced.mk ℤ R S P.carrier s p

private theorem intDictionaryTransport_pure (f : R →+* S) (P : ModuleCat.{uP} R)
    (d d' : Module ℤ P.carrier) (h : d = d') (s : S) (p : P) :
    (eqToIso (congrArg (intDictionaryObject f P) h)).hom.hom
        (intDictionaryPure f P d s p) = intDictionaryPure f P d' s p := by
  cases h
  rfl

private def nativePure (f : R →+* S) (P : ModuleCat.{uP} R) (s : S) (p : P) :
    (genericFunctor f).obj P :=
  letI := rightModule f
  letI := leftRightComm f
  letI : Module ℤ P.carrier := Module.compHom P.carrier (algebraMap ℤ R)
  TensorProduct.Balanced.mk ℤ R S P.carrier s p

private abbrev canonicalIntDictionary (P : ModuleCat.{uP} R) : Module ℤ P.carrier :=
  inferInstance

private theorem genericObj_dictionary (f : R →+* S) (P : ModuleCat.{uP} R) :
    (genericFunctor f).obj P =
      intDictionaryObject f P (Module.compHom P.carrier (algebraMap ℤ R)) := by
  rfl

private theorem dictionaryObj_canonical (f : R →+* S) (P : ModuleCat.{uP} R) :
    intDictionaryObject f P (inferInstance : Module ℤ P.carrier) = obj f P := by
  rfl

private theorem genericObj_dictionary_hom_pure (f : R →+* S)
    (P : ModuleCat.{uP} R) (s : S) (p : P) :
    (eqToIso (genericObj_dictionary f P)).hom.hom (nativePure f P s p) =
      intDictionaryPure f P (Module.compHom P.carrier (algebraMap ℤ R)) s p := by
  rfl

private theorem dictionaryObj_canonical_hom_pure (f : R →+* S)
    (P : ModuleCat.{uP} R) (s : S) (p : P) :
    (eqToIso (dictionaryObj_canonical f P)).hom.hom
        (intDictionaryPure f P (inferInstance : Module ℤ P.carrier) s p) =
      pure f P s p := by
  rfl

private theorem genericObjIso_dictionary (f : R →+* S) (P : ModuleCat.{uP} R) :
    genericObjIso f P =
      eqToIso (genericObj_dictionary f P) ≪≫
        eqToIso (congrArg (intDictionaryObject f P)
          (Subsingleton.elim
            (Module.compHom P.carrier (algebraMap ℤ R))
            (inferInstance : Module ℤ P.carrier))) ≪≫
        eqToIso (dictionaryObj_canonical f P) := by
  simp only [genericObjIso, eqToIso_trans]

private theorem genericObjIso_hom_pure (f : R →+* S) (P : ModuleCat.{uP} R)
    (s : S) (p : P) :
    (genericObjIso f P).hom.hom (nativePure f P s p) = pure f P s p := by
  let d : Module ℤ P.carrier := Module.compHom P.carrier (algebraMap ℤ R)
  let d' : Module ℤ P.carrier := canonicalIntDictionary P
  have h : d = d' := Subsingleton.elim _ _
  calc
    (genericObjIso f P).hom.hom (nativePure f P s p) =
        (eqToIso (dictionaryObj_canonical f P)).hom.hom
          ((eqToIso (congrArg (intDictionaryObject f P) h)).hom.hom
            ((eqToIso (genericObj_dictionary f P)).hom.hom
              (nativePure f P s p))) :=
      congrArg (fun e : (genericFunctor f).obj P ≅ obj f P =>
        e.hom.hom (nativePure f P s p)) (genericObjIso_dictionary f P)
    _ = (eqToIso (dictionaryObj_canonical f P)).hom.hom
        (intDictionaryPure f P d' s p) := by
      rw [genericObj_dictionary_hom_pure, intDictionaryTransport_pure f P d d' h s p]
    _ = pure f P s p := dictionaryObj_canonical_hom_pure f P s p

private theorem genericMap_pure (f : R →+* S) {P Q : ModuleCat.{uP} R}
    (g : P ⟶ Q) (s : S) (p : P) :
    ((genericFunctor f).map g).hom (nativePure f P s p) =
      nativePure f Q s (g.hom p) := by
  let := rightModule f
  let := leftRightComm f
  exact ModuleCat.BalancedTensor.Left.map_mk ℤ R S S g s p

/-- The actual extension functor uses the generic balanced-tensor functor,
with its objects transported to the same canonical integer-action carriers. -/
@[expose] def functor (f : R →+* S) :
    ModuleCat.{uP} R ⥤ ModuleCat.{max uS uP} S :=
  letI := rightModule f
  letI := leftRightComm f
  (ModuleCat.BalancedTensor.Left.functor ℤ R S S).copyObj (obj f)
    (fun P => eqToIso (by exact genericObj_eq f P))

private def genericCopyIso (f : R →+* S) : genericFunctor f ≅ functor f :=
  (genericFunctor f).isoCopyObj (obj f) (genericObjIso f)

private theorem genericCopyIso_hom_pure (f : R →+* S) (P : ModuleCat.{uP} R)
    (s : S) (p : P) :
    ((genericCopyIso f).hom.app P).hom (nativePure f P s p) = pure f P s p := by
  change (genericObjIso f P).hom.hom (nativePure f P s p) = pure f P s p
  exact genericObjIso_hom_pure f P s p

/-- The computational object of the same functor has its explicit original carrier view. -/
theorem functor_obj (f : R →+* S) (P : ModuleCat.{uP} R) :
    (functor f).obj P = ModuleCat.of S (tensor f P) :=
  rfl

/-- The induced map on pure representatives keeps its original module morphism. -/
theorem functor_map_pure (f : R →+* S) {P Q : ModuleCat.{uP} R}
    (g : P ⟶ Q) (s : S) (p : P) :
    ((functor f).map g).hom (pure f P s p) = pure f Q s (g.hom p) := by
  have hNat := (genericCopyIso f).hom.naturality g
  have hAt := ConcreteCategory.congr_hom hNat (nativePure f P s p)
  change ((genericCopyIso f).hom.app Q).hom
      (((genericFunctor f).map g).hom (nativePure f P s p)) =
    ((functor f).map g).hom
      (((genericCopyIso f).hom.app P).hom (nativePure f P s p)) at hAt
  rw [genericCopyIso_hom_pure] at hAt
  have hImage := genericMap_pure f g s p
  exact hAt.symm.trans
    ((congrArg (fun x : (genericFunctor f).obj Q =>
      ((genericCopyIso f).hom.app Q).hom x) hImage).trans
        (genericCopyIso_hom_pure f Q s (g.hom p)))

/-- The exact underlying quotient map of an original bundled module morphism. -/
theorem functor_map_hom (f : R →+* S) {P Q : ModuleCat.{uP} R} (g : P ⟶ Q) :
    ((functor f).map g).hom = linearMap f g.hom := by
  apply linearMap_ext f P
  intro s p
  exact (functor_map_pure f g s p).trans (linearMap_pure f g.hom s p).symm

/-- The extension functor inherits additivity from the generic balanced functor. -/
instance functorAdditive (f : R →+* S) : (functor.{uR,uS,uP} f).Additive := by
  let := rightModule f
  let := leftRightComm f
  let : (genericFunctor.{uR,uS,uP} f).Additive :=
    ModuleCat.BalancedTensor.Left.additive ℤ R S S
  exact Functor.additive_of_iso (genericCopyIso f)

private def coefficientBilinear (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) :
    S →ₗ[ℤ] P →ₗ[ℤ] S where
  toFun s := (LinearMap.mulLeft ℤ s).comp
    ((f.toAddMonoidHom.comp c.toAddMonoidHom).toIntLinearMap)
  map_add' s t := by
    apply LinearMap.ext
    intro p
    change (s + t) * f (c p) = s * f (c p) + t * f (c p)
    exact add_mul s t (f (c p))
  map_smul' z s := by
    apply LinearMap.ext
    intro p
    change (z • s) * f (c p) = z • (s * f (c p))
    exact smul_mul_assoc z s (f (c p))

private theorem coefficientBilinearBalanced (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) :
    letI := rightModule f
    ∀ (r : R) (s : S) (p : P),
      coefficientBilinear f c (op r • s) p = coefficientBilinear f c s (r • p) := by
  let := rightModule f
  intro r s p
  change (s * f r) * f (c p) = s * f (c (r • p))
  rw [c.map_smul, smul_eq_mul, map_mul, mul_assoc]

private def coefficientGround (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) : tensor f P →ₗ[ℤ] S :=
  letI := rightModule f
  TensorProduct.Balanced.lift (coefficientBilinear f c) (coefficientBilinearBalanced f c)

private theorem coefficientGround_pure (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) (s : S) (p : P) :
    coefficientGround f c (pure f P s p) = s * f (c p) := by
  let := rightModule f
  rw [pure_eq_mk]
  change TensorProduct.Balanced.lift (coefficientBilinear f c)
    (coefficientBilinearBalanced f c) (TensorProduct.Balanced.mk ℤ R S P s p) = _
  exact TensorProduct.Balanced.lift_mk (coefficientBilinear f c)
    (coefficientBilinearBalanced f c) s p

/-- Extend an actual `R` coordinate to an `S` coordinate on the balanced carrier. -/
def coefficient (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) : tensor f P →ₗ[S] S := by
  letI := rightModule f
  letI := leftRightComm f
  let l : tensor f P →ₗ[ℤ] S := coefficientGround f c
  refine { toFun := l, map_add' := l.map_add, map_smul' := ?_ }
  intro a x
  have he : l.toAddMonoidHom.comp
      ((TensorProduct.Balanced.leftAction ℤ R S S P a).toAddMonoidHom) =
      (AddMonoidHom.mulLeft a).comp l.toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ R S P
    intro s p
    change coefficientGround f c
      ((TensorProduct.Balanced.leftAction ℤ R S S P a) (pure f P s p)) =
        a * coefficientGround f c (pure f P s p)
    have hAction : (TensorProduct.Balanced.leftAction ℤ R S S P a)
        (pure f P s p) = pure f P (a * s) p := by
      simp only [pure_eq_mk]
      exact TensorProduct.Balanced.leftAction_mk ℤ R S S P a s p
    rw [hAction, coefficientGround_pure, coefficientGround_pure]
    exact mul_assoc a s (f (c p))
  exact DFunLike.congr_fun he x

private theorem coefficient_apply_linearMap (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) (x : tensor f P) :
    coefficient f c x = coefficientGround f c x :=
  rfl

/-- The coefficient formula follows the original homomorphism in the given order. -/
theorem coefficient_pure (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] (c : P →ₗ[R] R) (s : S) (p : P) :
    coefficient f c (pure f P s p) = s * f (c p) := by
  rw [coefficient_apply_linearMap]
  exact coefficientGround_pure f c s p

private def reconstruction (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] {n : ℕ} (a : Fin n → P) :
    (Fin n → S) →ₗ[S] tensor f P where
  toFun x := ∑ i, x i • pure f P 1 (a i)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' s x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

private def coordinates (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] {n : ℕ} (c : P →ₗ[R] (Fin n → R)) :
    tensor f P →ₗ[S] (Fin n → S) :=
  LinearMap.pi (fun i => coefficient f ((LinearMap.proj i).comp c))

private theorem extendedRetraction (f : R →+* S) {P : Type uP}
    [AddCommGroup P] [Module R P] {n : ℕ}
    (a : (Fin n → R) →ₗ[R] P) (c : P →ₗ[R] (Fin n → R))
    (hc : a.comp c = LinearMap.id) :
    (reconstruction f (fun i => a (Pi.single i 1))).comp (coordinates f c) =
      LinearMap.id := by
  classical
  apply linearMap_ext f P
  intro s p
  have hp : ∑ i, c p i • a (Pi.single i 1) = p := by
    have hsum : (∑ i, c p i • Pi.single i (1 : R)) = c p := by
      ext j
      simp [Pi.single_apply]
    calc
      _ = a (∑ i, c p i • Pi.single i (1 : R)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (a.map_smul (c p i) (Pi.single i 1)).symm
      _ = a (c p) := congrArg a hsum
      _ = p := DFunLike.congr_fun hc p
  change (∑ i, coefficient f ((LinearMap.proj i).comp c) (pure f P s p) •
      pure f P 1 (a (Pi.single i 1))) = pure f P s p
  simp only [coefficient_pure, LinearMap.comp_apply, LinearMap.proj_apply]
  calc
    _ = ∑ i, pure f P (s * f (c p i)) (a (Pi.single i 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_pure, mul_one]
    _ = ∑ i, pure f P s (c p i • a (Pi.single i 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact pure_balance f P (c p i) s (a (Pi.single i 1))
    _ = pure f P s (∑ i, c p i • a (Pi.single i 1)) := by rw [map_sum]
    _ = pure f P s p := congrArg (pure f P s) hp

/-- Scalar extension preserves finite projectivity using an actual finite retraction. -/
theorem finiteProjective (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] :
    Module.Finite S (tensor f P) ∧ Module.Projective S (tensor f P) := by
  obtain ⟨n,a,c,_,_,hc⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  let i := coordinates f c
  let r := reconstruction f (fun j => a (Pi.single j 1))
  have hr : r.comp i = LinearMap.id := extendedRetraction f a c hc
  have hsurj : Function.Surjective r := fun x => ⟨i x, DFunLike.congr_fun hr x⟩
  exact ⟨Module.Finite.of_surjective r hsurj, Module.Projective.of_split i r hr⟩

/-- The same finite-projective proof in the public functor's actual bundled object view. -/
theorem isFGProjective_obj (f : R →+* S) (P : FGProjectiveCat.{uP} R) :
    ModuleCat.isFGProjective S ((functor f).obj P.obj) := by
  rw [functor_obj]
  exact finiteProjective f P

/-- The canonical rank-`n` tensor coordinates; no rank-uniqueness property is assumed. -/
def finiteFreeTensorLinearEquiv (f : R →+* S) (n : ℕ) :
    tensor f (Fin n → R) ≃ₗ[S] (Fin n → S) := by
  classical
  let i := coordinates f (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R))
  let r := reconstruction f (fun j : Fin n => Pi.single j (1 : R))
  have hir : i.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply funext
    intro j
    change coefficient f ((LinearMap.proj j).comp (LinearMap.id :
      (Fin n → R) →ₗ[R] (Fin n → R)))
      (∑ k, x k • pure f (Fin n → R) 1 (Pi.single k 1)) = x j
    simp [map_sum, map_smul, coefficient_pure, Pi.single_apply, smul_eq_mul]
  have hri : r.comp i = LinearMap.id :=
    extendedRetraction f (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R))
      (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R)) (by ext x; rfl)
  exact LinearEquiv.ofLinearMap i r hir hri

/-- Actual free tensor coordinates send `s ⊗ x` to the row `s * f(xᵢ)`. -/
theorem finiteFreeTensorLinearEquiv_pure (f : R →+* S) (n : ℕ)
    (s : S) (x : Fin n → R) (j : Fin n) :
    finiteFreeTensorLinearEquiv f n (pure f (Fin n → R) s x) j = s * f (x j) := by
  unfold finiteFreeTensorLinearEquiv
  change coefficient f ((LinearMap.proj j).comp (LinearMap.id :
    (Fin n → R) →ₗ[R] (Fin n → R))) (pure f (Fin n → R) s x) = _
  exact coefficient_pure f _ s x

/-- The inverse coordinates are the original sum of unit-balanced basis classes. -/
theorem finiteFreeTensorLinearEquiv_symm (f : R →+* S) (n : ℕ) (x : Fin n → S) :
    (finiteFreeTensorLinearEquiv f n).symm x =
      ∑ j, x j • pure f (Fin n → R) 1 (Pi.single j 1) :=
  by
    unfold finiteFreeTensorLinearEquiv
    rfl

end ModuleCat.RingHomScalarExtension

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual noncommutative extension lifted to all finite projectives. -/
@[expose] def scalarExtension (f : R →+* S) :
    FGProjectiveCat.{uP} R ⥤ FGProjectiveCat.{max uS uP} S :=
  (ModuleCat.isFGProjective.{max uS uP} S).lift
    (toModuleCat ⋙ ModuleCat.RingHomScalarExtension.functor f)
    (fun P => ModuleCat.RingHomScalarExtension.isFGProjective_obj f P)

/-- The original module-object equation for the actual full-subcategory lift. -/
theorem scalarExtension_obj_obj (f : R →+* S) (P : FGProjectiveCat.{uP} R) :
    ((scalarExtension f).obj P).obj =
      (ModuleCat.RingHomScalarExtension.functor f).obj P.obj :=
  by
    dsimp only [scalarExtension, toModuleCat]
    exact ObjectProperty.ι_obj_lift_obj
      (ModuleCat.isFGProjective.{max uS uP} S)
      ((ModuleCat.isFGProjective.{uP} R).ι ⋙ ModuleCat.RingHomScalarExtension.functor f)
      (fun X => ModuleCat.RingHomScalarExtension.isFGProjective_obj f X) P

/-- Canonical module coordinates from the actual lifted object to its original tensor carrier. -/
def scalarExtensionCarrierLinearEquiv (f : R →+* S) (P : FGProjectiveCat.{uP} R) :
    (scalarExtension f).obj P ≃ₗ[S] ModuleCat.RingHomScalarExtension.tensor f P :=
  (eqToIso ((scalarExtension_obj_obj f P).trans
    (ModuleCat.RingHomScalarExtension.functor_obj f P.obj))).toLinearEquiv

private theorem scalarExtensionCarrierLinearEquiv_map_pure_computed
    (f : R →+* S) {P Q : FGProjectiveCat.{uP} R} (g : P ⟶ Q) (s : S) (p : P) :
    scalarExtensionCarrierLinearEquiv f Q
      (((scalarExtension f).map g).hom.hom
        ((scalarExtensionCarrierLinearEquiv f P).symm
          (ModuleCat.RingHomScalarExtension.pure f P s p))) =
      ModuleCat.RingHomScalarExtension.pure f Q s (g.hom.hom p) := by
  change ((ModuleCat.RingHomScalarExtension.functor f).map g.hom).hom
    (ModuleCat.RingHomScalarExtension.pure f P s p) = _
  exact ModuleCat.RingHomScalarExtension.functor_map_pure f g.hom s p

/-- The actual scalar-extension map retains the original morphism on every unit or pure class. -/
theorem scalarExtensionCarrierLinearEquiv_map_pure
    (f : R →+* S) {P Q : FGProjectiveCat.{uP} R} (g : P ⟶ Q) (s : S) (p : P) :
    scalarExtensionCarrierLinearEquiv f Q
      (((scalarExtension f).map g).hom.hom
        ((scalarExtensionCarrierLinearEquiv f P).symm
          (ModuleCat.RingHomScalarExtension.pure f P s p))) =
      ModuleCat.RingHomScalarExtension.pure f Q s (g.hom.hom p) :=
  scalarExtensionCarrierLinearEquiv_map_pure_computed f g s p

private theorem scalarExtensionCarrierLinearEquiv_naturality_computed
    (f : R →+* S) {P Q : FGProjectiveCat.{uP} R} (g : P ⟶ Q) :
    (scalarExtensionCarrierLinearEquiv f Q).toLinearMap.comp
        ((scalarExtension f).map g).hom.hom =
      (ModuleCat.RingHomScalarExtension.linearMap f g.hom.hom).comp
        (scalarExtensionCarrierLinearEquiv f P).toLinearMap := by
  have h : (scalarExtensionCarrierLinearEquiv f Q).toLinearMap.comp
      (((scalarExtension f).map g).hom.hom.comp
        (scalarExtensionCarrierLinearEquiv f P).symm.toLinearMap) =
      ModuleCat.RingHomScalarExtension.linearMap f g.hom.hom := by
    apply ModuleCat.RingHomScalarExtension.linearMap_ext f P
    intro s p
    exact (scalarExtensionCarrierLinearEquiv_map_pure_computed f g s p).trans
      (ModuleCat.RingHomScalarExtension.linearMap_pure f g.hom.hom s p).symm
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun h (scalarExtensionCarrierLinearEquiv f P x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply] using hx

/-- Whole-map naturality of the earned original scalar-extension carrier dictionaries. -/
theorem scalarExtensionCarrierLinearEquiv_naturality
    (f : R →+* S) {P Q : FGProjectiveCat.{uP} R} (g : P ⟶ Q) :
    (scalarExtensionCarrierLinearEquiv f Q).toLinearMap.comp
        ((scalarExtension f).map g).hom.hom =
      (ModuleCat.RingHomScalarExtension.linearMap f g.hom.hom).comp
        (scalarExtensionCarrierLinearEquiv f P).toLinearMap :=
  scalarExtensionCarrierLinearEquiv_naturality_computed f g

/-- The induced finite-projective functor is additive. -/
instance scalarExtensionAdditive (f : R →+* S) :
    (scalarExtension.{uR,uS,uP} f).Additive := by
  let F : FGProjectiveCat.{uP} R ⥤ ModuleCat.{max uS uP} S :=
    toModuleCat ⋙ ModuleCat.RingHomScalarExtension.functor f
  let P := ModuleCat.isFGProjective.{max uS uP} S
  let hF : ∀ X : FGProjectiveCat.{uP} R, P (F.obj X) :=
    fun X => ModuleCat.RingHomScalarExtension.isFGProjective_obj f X
  let hcomp : (P.lift F hF ⋙ P.ι).Additive :=
    Functor.additive_of_iso (P.liftCompιIso F hF).symm
  change (P.lift F hF).Additive
  exact Functor.additive_of_comp_faithful (P.lift F hF) P.ι

/-- Every split exact sequence is retained; no flatness of the target ring is required. -/
instance scalarExtensionExact (f : R →+* S) :
    (scalarExtension.{uR,uS,uP} f).IsExact :=
  ExactCategory.isExact_splitSource _

/-- Resize only the actual extension carrier through the canonical module equivalence. -/
@[expose] def ringScalarExtension (f : R →+* S) :
    FGProjectiveCat.{uR} R ⥤ FGProjectiveCat.{uS} S :=
  scalarExtension f ⋙ (universeEquivalence.{uS,uR} S).functor

/-- Canonical carrier resizing retains the same additive map. -/
instance ringScalarExtensionAdditive (f : R →+* S) : (ringScalarExtension f).Additive := by
  dsimp only [ringScalarExtension]
  infer_instance

/-- The canonical ring-universe extension is exact from the split source. -/
instance ringScalarExtensionExact (f : R →+* S) : (ringScalarExtension f).IsExact :=
  ExactCategory.isExact_splitSource _

/-- Source and target module carriers are resized independently through
actual linear equivalences. -/
@[expose] def resizedScalarExtension (f : R →+* S) :
    FGProjectiveCat.{max uR uMR} R ⥤ FGProjectiveCat.{max uS uMS} S :=
  scalarExtension f ⋙
    (universeEquivalence.{uS,max uR uMR} S).functor ⋙
      (universeEquivalence.{uS,uMS} S).inverse

/-- The independently resized extension still acts additively on every original map. -/
instance resizedScalarExtensionAdditive (f : R →+* S) :
    (resizedScalarExtension.{uR,uS,uMR,uMS} f).Additive := by
  dsimp only [resizedScalarExtension]
  infer_instance

/-- Independent carrier resizing retains the split exact structure. -/
instance resizedScalarExtensionExact (f : R →+* S) :
    (resizedScalarExtension.{uR,uS,uMR,uMS} f).IsExact :=
  ExactCategory.isExact_splitSource _

/-- The canonical actual linear coordinates from the resized object to its original tensor. -/
def resizedScalarExtensionLinearEquiv (f : R →+* S)
    (P : FGProjectiveCat.{max uR uMR} R) :
    (resizedScalarExtension.{uR,uS,uMR,uMS} f).obj P ≃ₗ[S]
      ModuleCat.RingHomScalarExtension.tensor f P :=
  ((UniverseEquivalence.liftLinearEquiv.{uS,uMS} S
      ((universeEquivalence.{uS,max uR uMR} S).functor.obj ((scalarExtension f).obj P))).trans
    (UniverseEquivalence.shrinkLinearEquiv.{uS,max uR uMR} S ((scalarExtension f).obj P))).trans
      (scalarExtensionCarrierLinearEquiv f P)

/-- Actual object/Hom lifting on both sides of the independently resized extension. -/
@[expose] def liftedScalarExtension (f : R →+* S) :
    CategoryUniverseLift.category.{uR,uMR,uOR,uHR} R ⥤
      CategoryUniverseLift.category.{uS,uMS,uOS,uHS} S :=
  CategoryUniverseLift.downFunctor.{uR,uMR,uOR,uHR} R ⋙
    resizedScalarExtension.{uR,uS,uMR,uMS} f ⋙
      CategoryUniverseLift.upFunctor.{uS,uMS,uOS,uHS} S

/-- The two independent category lifts preserve the same addition of linear maps. -/
instance liftedScalarExtensionAdditive (f : R →+* S) :
    (liftedScalarExtension.{uR,uS,uMR,uMS,uOR,uHR,uOS,uHS} f).Additive := by
  dsimp only [liftedScalarExtension]
  infer_instance

/-- The actual independently lifted scalar-extension functor is split exact. -/
instance liftedScalarExtensionExact (f : R →+* S) :
    (liftedScalarExtension.{uR,uS,uMR,uMS,uOR,uHR,uOS,uHS} f).IsExact :=
  ExactCategory.isExact_splitSource _

end FGProjectiveCat
