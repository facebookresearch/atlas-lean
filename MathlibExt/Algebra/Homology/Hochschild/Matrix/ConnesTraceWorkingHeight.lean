/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesWorkingHeight
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.ConnesTrace
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatizationWorkingHeight

/-!
# The Connes quotient trace in independent coefficient worlds

Let k be a commutative ring and A an associative unital k-algebra, in
independent carrier worlds u and v. For an additional height z, lift
the cyclic bicomplex and its first-column cokernel to H = max(u,v,z).
The generalized matrix trace induces
T^H : Cλ^H(Mat_r(A)) → Cλ^H(A). On lifted tensor representatives,
T_n^H(q_n^Mat(up(x))) = q_n^A(up(T_n(x))), where T_n is the
closed-cycle generalized trace and Cλ is the quotient by 1−t.

For a k-algebra B in an independent world w and a unital k-algebra map
f : A → B, put both quotient complexes at H = max(u,v,w,z).
The square T_B^H ∘ Cλ^H(Mat_r(f)) = Cλ^H(f) ∘ T_A^H commutes.
No equality between the coefficient carrier worlds is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u v w z

namespace ModuleCat.Algebra.Hochschild.Matrix

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k, a k-algebra A, r ≥ 0 and
H = max(u,v,z), generalized trace defines
Cλ^H(Mat_r(A)) → Cλ^H(A). The complexes are the first-column cyclic
cokernels at height H, and their degree maps take a lifted matrix
tensor class to the class of its lifted generalized trace. -/
def connesTraceAtHeight (r : ℕ) :
    NonUnital.connesComplexAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) ⟶
      NonUnital.connesComplexAtHeight.{u,v,z} k A :=
  (NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A)).inv ≫
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (connesTrace k A r) ≫
        (NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom

/-- For a k-algebra A, r,n ≥ 0, H = max(u,v,z) and
x ∈ Mat_r(A) ⊗[k] Mat_r(A)^⊗n, the chosen-height trace satisfies
T_n^H(q_n^Mat(up(x))) = q_n^A(up(T_n(x))).
Here the up maps lift the coefficient-first tensor terms to height H,
and T_n sums the entries around every closed matrix-index cycle. -/
theorem connesTraceAtHeight_projection_apply (r n : ℕ)
    (x : Matrix (Fin r) (Fin r) A ⊗[k] TensorPower k n (Matrix (Fin r) (Fin r) A)) :
    ((connesTraceAtHeight.{u,v,z} k A r).f n).hom
        ((NonUnital.connesProjectionAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n).hom
          (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k
        (Matrix (Fin r) (Fin r) A) n x)) =
      (NonUnital.connesProjectionAtHeight.{u,v,z} k A n).hom
        (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k A n
        (generalizedTrace k (Fin r) (A := A) (M := A) n x)) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v z} k) (ComplexShape.down ℕ) n
  let eM : (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NonUnital.connesComplex k (Matrix (Fin r) (Fin r) A))).X n ≅
        (NonUnital.connesComplexAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A)).X n :=
    E.mapIso (NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A))
  let eA : (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NonUnital.connesComplex k A)).X n ≅
        (NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
    E.mapIso (NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A)
  let qM := connesProjection k (Matrix (Fin r) (Fin r) A) n
  let qA := connesProjection k A n
  have hM : (NonUnital.connesProjectionAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n).hom
      (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k
        (Matrix (Fin r) (Fin r) A) n x) = eM.hom.hom (ChevalleyEilenberg.connesTermUpAtHeight.{u,v,z} k
        (Matrix (Fin r) (Fin r) A) n (qM.hom x)) := by
    have h := E.congr_map
      (NonUnital.connesComplexLiftIsoAtHeight_π.{u,v,z} k (Matrix (Fin r) (Fin r) A))
    simp only [E, HomologicalComplex.eval_map, HomologicalComplex.eval_obj] at h
    have hv := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k
        (Matrix (Fin r) (Fin r) A) n x)
    exact hv.symm
  have hA : eA.hom.hom
      (ChevalleyEilenberg.connesTermUpAtHeight.{u,v,z} k A n
        (qA.hom (generalizedTrace k (Fin r) (A := A) (M := A) n x))) =
        (NonUnital.connesProjectionAtHeight.{u,v,z} k A n).hom
          (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k A n
        (generalizedTrace k (Fin r) (A := A) (M := A) n x)) := by
    have h := E.congr_map (NonUnital.connesComplexLiftIsoAtHeight_π.{u,v,z} k A)
    simp only [E, HomologicalComplex.eval_map, HomologicalComplex.eval_obj] at h
    have hv := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
      (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k A n
        (generalizedTrace k (Fin r) (A := A) (M := A) n x))
    exact hv
  have ht : ((connesTrace k A r).f n).hom (qM.hom x) =
      qA.hom (generalizedTrace k (Fin r) (A := A) (M := A) n x) := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (connesProjection_traceComponent k A r n)) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  change eA.hom.hom (ULift.up (((connesTrace k A r).f n).hom
    (eM.inv.hom ((NonUnital.connesProjectionAtHeight.{u,v,z} k
      (Matrix (Fin r) (Fin r) A) n).hom (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,z} k
        (Matrix (Fin r) (Fin r) A) n x))).down)) = _
  have hInv : eM.inv.hom (eM.hom.hom
      (ChevalleyEilenberg.connesTermUpAtHeight.{u,v,z} k
        (Matrix (Fin r) (Fin r) A) n (qM.hom x))) =
        ChevalleyEilenberg.connesTermUpAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n (qM.hom x) :=
    ModuleCat.inv_hom_apply eM _
  rw [hM, hInv]
  exact (congrArg (fun y => eA.hom.hom (ULift.up y)) ht).trans hA

variable {B : Type w} [Ring B] [Algebra k B]

/-- For a commutative ring k, k-algebras A and B in independent
carrier worlds v and w, a unital k-algebra map f : A → B and r ≥ 0,
put all complexes at H = max(u,v,w,z). The square
Cλ^H(f) ∘ T_A^H = T_B^H ∘ Cλ^H(Mat_r(f))
commutes from Cλ^H(Mat_r(A)) to Cλ^H(B).
The extra lift height z is arbitrary. -/
theorem connesTraceAtHeight_naturality (f : A →ₐ[k] B) (r : ℕ) :
    connesTraceAtHeight.{u,v,max u v w z} k A r ≫
        NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f.toNonUnitalAlgHom =
      NonUnital.connesComplexHomAtHeight.{u,v,w,z} k (Matrix (Fin r) (Fin r) A)
          (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom ≫
        connesTraceAtHeight.{u,w,max u v w z} k B r := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hq : Epi (NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k
      (Matrix (Fin r) (Fin r) A) n) := by
    change Epi ((HomologicalComplex.eval (ModuleCat.{max u v w z} k) (ComplexShape.down ℕ) n).map
      (cokernel.π ((NonUnital.cyclicBicomplexAtHeight.{u,v,max u v w z} k
        (Matrix (Fin r) (Fin r) A)).d 1 0)))
    infer_instance
  apply (cancel_epi (NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k
    (Matrix (Fin r) (Fin r) A) n)).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  let y : Matrix (Fin r) (Fin r) A ⊗[k] TensorPower k n (Matrix (Fin r) (Fin r) A) := x
  change ((NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f.toNonUnitalAlgHom).f n).hom
      (((connesTraceAtHeight.{u,v,max u v w z} k A r).f n).hom
        ((NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k (Matrix (Fin r) (Fin r) A) n).hom
          (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,max u v w z} k
            (Matrix (Fin r) (Fin r) A) n y))) =
    ((connesTraceAtHeight.{u,w,max u v w z} k B r).f n).hom
      (((NonUnital.connesComplexHomAtHeight.{u,v,w,z} k (Matrix (Fin r) (Fin r) A)
        (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom).f n).hom
          ((NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k (Matrix (Fin r) (Fin r) A) n).hom
            (ChevalleyEilenberg.connesConsUpAtHeight.{u,v,max u v w z} k
            (Matrix (Fin r) (Fin r) A) n y)))
  rw [connesTraceAtHeight_projection_apply]
  let g := generalizedTrace k (Fin r) (A := A) (M := A) n
  let qA := NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k A n
  let qB := NonUnital.connesProjectionAtHeight.{u,w,max u v w z} k B n
  let qMA := NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k (Matrix (Fin r) (Fin r) A) n
  let qMB := NonUnital.connesProjectionAtHeight.{u,w,max u v w z} k (Matrix (Fin r) (Fin r) B) n
  let cA := (NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f.toNonUnitalAlgHom).f n
  let cM := (NonUnital.connesComplexHomAtHeight.{u,v,w,z} k (Matrix (Fin r) (Fin r) A)
    (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom).f n
  let upA := ChevalleyEilenberg.connesConsUpAtHeight.{u,v,max u v w z} k A n
  let upB := ChevalleyEilenberg.connesConsUpAtHeight.{u,w,max u v w z} k B n
  let upMA := ChevalleyEilenberg.connesConsUpAtHeight.{u,v,max u v w z} k
    (Matrix (Fin r) (Fin r) A) n
  let upMB := ChevalleyEilenberg.connesConsUpAtHeight.{u,w,max u v w z} k
    (Matrix (Fin r) (Fin r) B) n
  let tB := (connesTraceAtHeight.{u,w,max u v w z} k B r).f n
  have hA := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (NonUnital.connesProjectionAtHeight_naturality.{u,v,w,z} k A f.toNonUnitalAlgHom n)) (upA (g y))
  change cA.hom (qA.hom (upA (g y))) = qB.hom
    ((((NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z} f.toNonUnitalAlgHom).f 0).f n).hom
      (upA (g y))) at hA
  have hvA : (((NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z} f.toNonUnitalAlgHom).f 0).f n).hom
      (upA (g y)) = upB (TensorPower.consLevelMap (f : A →ₗ[k] B) n (g y)) :=
    NonUnital.cyclicBicomplexMapAtHeight_f_f_up.{u,v,w,z} f.toNonUnitalAlgHom 0 n (g y)
  have hA' := hA.trans (congrArg qB.hom hvA)
  have hM := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (NonUnital.connesProjectionAtHeight_naturality.{u,v,w,z} k (Matrix (Fin r) (Fin r) A)
      (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom n)) (upMA y)
  change cM.hom (qMA.hom (upMA y)) = qMB.hom
    ((((NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z}
      (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom).f 0).f n).hom (upMA y)) at hM
  have hvM : (((NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z}
      (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom).f 0).f n).hom (upMA y) =
    upMB (TensorPower.consLevelMap ((f.mapMatrix (m := Fin r)) :
      Matrix (Fin r) (Fin r) A →ₗ[k] Matrix (Fin r) (Fin r) B) n y) :=
    NonUnital.cyclicBicomplexMapAtHeight_f_f_up.{u,v,w,z}
      (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom 0 n y
  have hM' := hM.trans (congrArg qMB.hom hvM)
  have hG := LinearMap.congr_fun (generalizedTrace_naturality k (Fin r) n
    (f : A →ₗ[k] B) (f : A →ₗ[k] B)) y
  simp only [LinearMap.comp_apply] at hG
  have hTr := connesTraceAtHeight_projection_apply.{u,w,max u v w z} k B r n
    (TensorPower.consLevelMap ((f.mapMatrix (m := Fin r)) :
      Matrix (Fin r) (Fin r) A →ₗ[k] Matrix (Fin r) (Fin r) B) n y)
  exact hA'.trans ((congrArg (fun v => qB.hom (upB v)) hG).trans
    (hTr.symm.trans (congrArg tB.hom hM'.symm)))


end ModuleCat.Algebra.Hochschild.Matrix
