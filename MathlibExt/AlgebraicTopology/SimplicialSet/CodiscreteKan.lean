/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# Codiscrete nerves are Kan complexes

The nerve of a codiscrete category is a Kan complex. In homogeneous coordinates an
`n`-simplex is `Fin (n+1) → X`. A horn `Λ[m+2, i] → nerve (Codiscrete X)` is filled
by evaluating its vertices: `G p` is the `0`-simplex of the horn at `p` obtained via
`hornVertexMap`. Face compatibility uses factorization through `stdVertex` and
`SSet.horn.ι`/`stdSimplex.δ`, matching `G ∘ j.succAbove` with the given faces.
Dimension one is treated separately: `Λ[1, i]` has a single vertex, and the filler is
the constant map at that vertex via `otherFin`. The proof covers empty types and
includes outer horns.
-/

@[expose] public section

namespace CategoryTheory.Codiscrete

open CategoryTheory Simplicial SSet Opposite

universe u

noncomputable section

variable {X : Type u}

private def codiscreteSimplex {n : ℕ} (f : Fin (n + 1) → X) :
    nerve (Codiscrete X) _⦋n⦌ :=
  (equivFun (X := X) (n := n)).symm f

private def codiscreteYoneda {n : ℕ} (f : Fin (n + 1) → X) :
    Δ[n] ⟶ nerve (Codiscrete X) :=
  SSet.yonedaEquiv.symm (codiscreteSimplex f)

@[simp]
private lemma yonedaEquiv_codiscreteYoneda {n : ℕ} (f : Fin (n + 1) → X) :
    SSet.yonedaEquiv (codiscreteYoneda (X := X) f) = codiscreteSimplex f := by
  simp [codiscreteYoneda]

@[simp]
private lemma equivFun_codiscreteSimplex {n : ℕ} (f : Fin (n + 1) → X) :
    equivFun (codiscreteSimplex (X := X) f) = f := by
  simp [codiscreteSimplex]

private def funOfYoneda {n : ℕ} (φ : Δ[n] ⟶ nerve (Codiscrete X)) :
    Fin (n + 1) → X :=
  equivFun (SSet.yonedaEquiv φ)

@[simp]
private lemma funOfYoneda_codiscreteYoneda {n : ℕ} (f : Fin (n + 1) → X) :
    funOfYoneda (codiscreteYoneda (X := X) f) = f := by
  simp [funOfYoneda]

@[simp]
private lemma codiscreteYoneda_funOfYoneda {n : ℕ}
    (φ : Δ[n] ⟶ nerve (Codiscrete X)) :
    codiscreteYoneda (funOfYoneda φ) = φ := by
  apply SSet.yonedaEquiv.injective
  simp [funOfYoneda, codiscreteSimplex]

private lemma δ_comp_codiscreteYoneda {n : ℕ} (i : Fin (n + 2))
    (f : Fin (n + 2) → X) :
    stdSimplex.δ i ≫ codiscreteYoneda (X := X) f =
      codiscreteYoneda (f ∘ i.succAbove) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  have : (nerve (Codiscrete X)).δ i (codiscreteSimplex f) =
      codiscreteSimplex (f ∘ i.succAbove) := by
    apply (equivFun (X := X)).injective
    ext k
    rfl
  simp [this]

private def otherFin : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

private lemma otherFin_ne (i : Fin 2) : otherFin i ≠ i := by
  fin_cases i <;> simp [otherFin]

private lemma eq_otherFin_of_ne {j i : Fin 2} (hj : j ≠ i) : j = otherFin i := by
  fin_cases i <;> fin_cases j <;> simp_all [otherFin]

private def stdVertex {n : ℕ} (p : Fin (n + 1)) : Δ[0] ⟶ Δ[n] :=
  SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm p)

private lemma stdVertex_comp_δ {n : ℕ} (j : Fin (n + 2)) (q : Fin (n + 1)) :
    stdVertex (n := n) q ≫ stdSimplex.δ j = stdVertex (j.succAbove q) := by
  calc stdVertex q ≫ stdSimplex.δ j
      = SSet.yonedaEquiv.symm ((stdSimplex.δ j).app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm q)) := by
          unfold stdVertex
          rw [SSet.yonedaEquiv_symm_comp]
    _ = SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (j.succAbove q)) := rfl
    _ = stdVertex (j.succAbove q) := rfl

private def hornVertex {m : ℕ} (i : Fin (m + 3)) (p : Fin (m + 3)) :
    (Λ[m + 2, i] : SSet).obj (op ⦋0⦌) where
  val := stdSimplex.obj₀Equiv.symm p
  property := by
    have h : (SSet.horn (m + 2) i).obj (op ⦋0⦌) = ⊤ := SSet.horn_obj_zero m i
    rw [h]
    trivial

private def hornVertexMap {m : ℕ} (i : Fin (m + 3)) (p : Fin (m + 3)) :
    Δ[0] ⟶ (Λ[m + 2, i] : SSet) :=
  SSet.yonedaEquiv.symm (hornVertex i p)

private lemma hornVertexMap_ι {m : ℕ} (i : Fin (m + 3)) (p : Fin (m + 3)) :
    hornVertexMap i p ≫ (SSet.horn (m + 2) i).ι = stdVertex p := by
  unfold hornVertexMap
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

private lemma stdVertex_comp_horn_ι_eq_hornVertexMap {m : ℕ}
    (i j : Fin (m + 3)) (hj : j ≠ i) (q : Fin (m + 2)) :
    stdVertex q ≫ SSet.horn.ι i j hj = hornVertexMap i (j.succAbove q) := by
  have h_mono : Mono (SSet.horn (m + 2) i).ι := inferInstance
  apply (cancel_mono (SSet.horn (m + 2) i).ι).1
  calc (stdVertex q ≫ SSet.horn.ι i j hj) ≫ (SSet.horn (m + 2) i).ι
      = stdVertex q ≫ (SSet.horn.ι i j hj ≫ (SSet.horn (m + 2) i).ι) := by rw [Category.assoc]
    _ = stdVertex q ≫ stdSimplex.δ j := by rw [SSet.horn.ι_ι]
    _ = stdVertex (j.succAbove q) := stdVertex_comp_δ j q
    _ = hornVertexMap i (j.succAbove q) ≫ (SSet.horn (m + 2) i).ι := by rw [hornVertexMap_ι]

private lemma funOfYoneda_vertex_comp {n : ℕ}
    (f : Δ[n] ⟶ nerve (Codiscrete X)) (q : Fin (n + 1)) :
    funOfYoneda (stdVertex q ≫ f) 0 = funOfYoneda f q := by
  have h1 : SSet.yonedaEquiv (stdVertex q ≫ f) =
      f.app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm q) := by
    calc SSet.yonedaEquiv (stdVertex q ≫ f)
        = SSet.yonedaEquiv (SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm q) ≫ f) := rfl
      _ = SSet.yonedaEquiv (SSet.yonedaEquiv.symm (f.app _ (stdSimplex.obj₀Equiv.symm q))) := by
          rw [SSet.yonedaEquiv_symm_comp]
      _ = f.app _ (stdSimplex.obj₀Equiv.symm q) := by
          simp only [SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_const]
  have h2 : stdSimplex.obj₀Equiv.symm q =
      stdSimplex.objEquiv.symm (SimplexCategory.const _ _ q) := rfl
  have h3 : f.app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm q) =
      (nerve (Codiscrete X)).map (SimplexCategory.const _ _ q).op
        (SSet.yonedaEquiv f) := by
    calc f.app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm q)
        = f.app (op ⦋0⦌) (stdSimplex.objEquiv.symm (SimplexCategory.const _ _ q)) := by rw [h2]
      _ = (SSet.yonedaEquiv.symm (SSet.yonedaEquiv f)).app _
            (stdSimplex.objEquiv.symm (SimplexCategory.const _ _ q)) := by
              rw [SSet.yonedaEquiv.symm_apply_apply]
      _ = (nerve (Codiscrete X)).map (SimplexCategory.const _ _ q).op
            (SSet.yonedaEquiv f) := by rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  simp only [funOfYoneda, h1, h3]
  rfl

/-- The nerve of a codiscrete category is a Kan complex, including empty types and
outer horns. The filler is built in homogeneous coordinates by reading vertex data;
`n = 0` uses constant extension via `otherFin`. -/
theorem nerve_codiscrete_kanComplex (X : Type u) :
    SSet.KanComplex (nerve (Codiscrete X)) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  cases n with
  | zero =>
    let jcan : Fin 2 := otherFin i
    have hjcan_ne : jcan ≠ i := otherFin_ne i
    let a : X := funOfYoneda (f jcan hjcan_ne) 0
    let G : Fin 2 → X := fun _ => a
    refine ⟨codiscreteYoneda G, fun j hj => ?_⟩
    have hj_eq : j = jcan := eq_otherFin_of_ne hj
    subst hj_eq
    have h_proof_eq : hj = hjcan_ne := Subsingleton.elim _ _
    rw [h_proof_eq]
    have hG : G ∘ jcan.succAbove = funOfYoneda (f jcan hjcan_ne) := by
      ext q
      fin_cases q
      simp [G, a]
    rw [δ_comp_codiscreteYoneda, hG, codiscreteYoneda_funOfYoneda]
  | succ m =>
    let φ : (Λ[m + 2, i] : SSet) ⟶ nerve (Codiscrete X) := hf.desc
    have hf_desc_eq : ∀ (j : Fin (m + 3)) (hj : j ≠ i),
        SSet.horn.ι i j hj ≫ φ = f j hj :=
      fun j hj => hf.ι_desc j hj
    let G : Fin (m + 3) → X := fun p =>
      funOfYoneda (hornVertexMap i p ≫ φ) 0
    have hG_eq : ∀ (j : Fin (m + 3)) (hj : j ≠ i) (q : Fin (m + 2)),
        G (j.succAbove q) = funOfYoneda (f j hj) q := by
      intro j hj q
      calc G (j.succAbove q)
          = funOfYoneda (hornVertexMap i (j.succAbove q) ≫ φ) 0 := rfl
        _ = funOfYoneda ((stdVertex q ≫ SSet.horn.ι i j hj) ≫ φ) 0 := by
            rw [← stdVertex_comp_horn_ι_eq_hornVertexMap i j hj q]
        _ = funOfYoneda (stdVertex q ≫ (SSet.horn.ι i j hj ≫ φ)) 0 := by rw [Category.assoc]
        _ = funOfYoneda (stdVertex q ≫ f j hj) 0 := by rw [hf_desc_eq j hj]
        _ = funOfYoneda (f j hj) q := funOfYoneda_vertex_comp _ q
    refine ⟨codiscreteYoneda G, fun j hj => ?_⟩
    rw [δ_comp_codiscreteYoneda]
    apply SSet.yonedaEquiv.injective
    simp only [yonedaEquiv_codiscreteYoneda]
    apply (equivFun (X := X) (n := m + 1)).injective
    ext q
    exact hG_eq j hj q

/-- `functorToSSet.obj X` is Kan: it is `nerve (Codiscrete X)` up to definitional
equality, hence inherits the homogeneous-coordinate Kan filler, including the
separate one-dimensional case and outer horns. -/
theorem kanComplex_functorToSSet_obj (X : Type u) :
    SSet.KanComplex (functorToSSet.obj X) := by
  simpa [functorToSSet_obj] using nerve_codiscrete_kanComplex X

end

end CategoryTheory.Codiscrete
