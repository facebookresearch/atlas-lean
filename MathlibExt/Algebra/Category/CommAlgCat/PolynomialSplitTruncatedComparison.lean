/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitDegreeExtension

/-!
# Extension of truncated polynomial comparisons

A degree-zero map of augmented simplicial k-algebras over A gives a comparison on the zero
truncation. More generally, let P be polynomial-split, let Q's normalized additive augmentation
be a quasi-isomorphism, and fix a comparison H through degree n.

The successor comparison uses its new polynomial lift in degree n+1 and retains H in all lower
degrees. Its naturality holds for every morphism in the truncated simplex category, including
the new endomorphisms. Restriction to degrees at most n returns H as a whole augmented morphism.

The ring k is any commutative ring. Its universe u and the algebra carrier parameter v are
independent; the diagrams use max(u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialSplitTruncatedComparison

open PolynomialSplitDegreeExtension

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (n : ℕ) (H : TruncatedComparison k A P Q n)
  (hQ : additiveResolutionCondition k A Q)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and f:P₀→Q₀ a
degree-zero map commuting with augmentation. For m≤0, transport f along m=0 to obtain the
zero-truncated component Pₘ→Qₘ. -/
def zeroComponent
    (f : Over.mk (P.hom.app (op ⦋0⦌)) ⟶ Over.mk (Q.hom.app (op ⦋0⦌)))
    (m : ℕ) (hm : m ≤ 0) : P.left.obj (op ⦋m⦌) ⟶ Q.left.obj (op ⦋m⦌) :=
  eqToHom (congrArg (fun l => P.left.obj (op ⦋l⦌)) (Nat.eq_zero_of_le_zero hm)) ≫ f.left ≫
    eqToHom (congrArg (fun l => Q.left.obj (op ⦋l⦌)) (Nat.eq_zero_of_le_zero hm).symm)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and f:P₀→Q₀ a
degree-zero map commuting with augmentation. For m,l≤0 and θ:op[m]→op[l], P(θ) followed by the
l-component equals the m-component followed by Q(θ). -/
theorem zeroComponent_naturality
    (f : Over.mk (P.hom.app (op ⦋0⦌)) ⟶ Over.mk (Q.hom.app (op ⦋0⦌)))
    {m l : ℕ} (hm : m ≤ 0) (hl : l ≤ 0) (θ : op ⦋m⦌ ⟶ op ⦋l⦌) :
    P.left.map θ ≫ zeroComponent f l hl = zeroComponent f m hm ≫ Q.left.map θ := by
  obtain rfl := Nat.eq_zero_of_le_zero hm
  obtain rfl := Nat.eq_zero_of_le_zero hl
  have hθ : θ = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    exact SimplexCategory.isTerminalZero.hom_ext _ _
  subst θ
  simp

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and f:P₀→Q₀ a
degree-zero map commuting with augmentation. Each zero-truncated component commutes with the
augmentations Pₘ→A and Qₘ→A. -/
theorem zeroComponent_augmentation
    (f : Over.mk (P.hom.app (op ⦋0⦌)) ⟶ Over.mk (Q.hom.app (op ⦋0⦌)))
    (m : ℕ) (hm : m ≤ 0) :
    zeroComponent f m hm ≫ Q.hom.app (op ⦋m⦌) = P.hom.app (op ⦋m⦌) := by
  obtain rfl := Nat.eq_zero_of_le_zero hm
  change (eqToHom rfl ≫ f.left ≫ eqToHom rfl) ≫ Q.hom.app (op ⦋0⦌) = P.hom.app (op ⦋0⦌)
  have h : f.left ≫ Q.hom.app (op ⦋0⦌) = P.hom.app (op ⦋0⦌) := by
    change f.left ≫ (Over.mk (Q.hom.app (op ⦋0⦌))).hom = (Over.mk (P.hom.app (op ⦋0⦌))).hom
    exact f.w
  exact ((congrArg (fun a => a ≫ Q.hom.app (op ⦋0⦌))
    ((Category.id_comp f.left).trans (Category.comp_id f.left))).trans h)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and f:P₀→Q₀ a
degree-zero map commuting with augmentation. Its transported components and their naturality
define an augmented comparison truncated through degree zero. -/
def ofZero (f : Over.mk (P.hom.app (op ⦋0⦌)) ⟶ Over.mk (Q.hom.app (op ⦋0⦌))) :
    TruncatedComparison k A P Q 0 :=
  Over.homMk
    { app Δ := zeroComponent f Δ.unop.obj.len Δ.unop.property
      naturality {Δ Δ'} θ := zeroComponent_naturality f Δ.unop.property Δ'.unop.property θ.unop.hom.op }
    (by
      apply NatTrans.ext
      funext Δ
      exact zeroComponent_augmentation f Δ.unop.obj.len Δ.unop.property)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and f:P₀→Q₀ a
degree-zero map commuting with augmentation. The degree-zero component of the resulting
truncated comparison is f. -/
@[simp]
theorem ofZero_component (f : Over.mk (P.hom.app (op ⦋0⦌)) ⟶ Over.mk (Q.hom.app (op ⦋0⦌))) :
    component 0 (ofZero f) 0 le_rfl = f.left := by
  simp [component, ofZero, zeroComponent]

private theorem incoming (m : ℕ) (hm : m ≤ n) (θ : op ⦋m⦌ ⟶ op ⦋n + 1⦌) :
    P.left.map θ ≫ degreeMap s n H hQ = component n H m hm ≫ Q.left.map θ := by
  let e := factorThruImage θ.unop
  let j := image.ι θ.unop
  have hd : (image θ.unop).len ≤ n := (SimplexCategory.len_le_of_mono j).trans hm
  have hθ : j.op ≫ e.op = θ := by
    apply Quiver.Hom.unop_inj
    simp [e, j]
  have hj := component_naturality n H hm hd j.op
  have he := degreeMap_epi_naturality s n H hQ (image θ.unop).len hd e.op
  calc
    P.left.map θ ≫ degreeMap s n H hQ =
        P.left.map j.op ≫ (P.left.map e.op ≫ degreeMap s n H hQ) := by
      have hmap : P.left.map θ = P.left.map j.op ≫ P.left.map e.op :=
        (congrArg P.left.map hθ.symm).trans (P.left.map_comp j.op e.op)
      exact (congrArg (fun a => a ≫ degreeMap s n H hQ) hmap).trans (Category.assoc _ _ _)
    _ = P.left.map j.op ≫ (component n H (image θ.unop).len hd ≫ Q.left.map e.op) := by rw [he]
    _ = (P.left.map j.op ≫ component n H (image θ.unop).len hd) ≫ Q.left.map e.op :=
      (Category.assoc _ _ _).symm
    _ = (component n H m hm ≫ Q.left.map j.op) ≫ Q.left.map e.op := by rw [hj]
    _ = component n H m hm ≫ Q.left.map θ :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => component n H m hm ≫ a)
          ((Q.left.map_comp j.op e.op).symm.trans (congrArg Q.left.map hθ)))

private theorem outgoing (m : ℕ) (hm : m ≤ n) (θ : op ⦋n + 1⦌ ⟶ op ⦋m⦌) :
    P.left.map θ ≫ component n H m hm = degreeMap s n H hQ ≫ Q.left.map θ := by
  have hnot : ¬ Function.Surjective θ.unop.toOrderHom := by
    intro h
    let _ : Epi θ.unop := SimplexCategory.epi_iff_surjective.mpr h
    have hlen := SimplexCategory.len_le_of_epi θ.unop
    change n + 1 ≤ m at hlen
    omega
  obtain ⟨i, g, hg⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ.unop hnot
  have hθ : (SimplexCategory.δ i).op ≫ g.op = θ := by
    apply Quiver.Hom.unop_inj
    simpa using hg.symm
  have hgH := component_naturality n H le_rfl hm g.op
  calc
    P.left.map θ ≫ component n H m hm =
        P.left.δ i ≫ (P.left.map g.op ≫ component n H m hm) := by
      have hmap : P.left.map θ = P.left.δ i ≫ P.left.map g.op :=
        (congrArg P.left.map hθ.symm).trans (P.left.map_comp (SimplexCategory.δ i).op g.op)
      exact (congrArg (fun a => a ≫ component n H m hm) hmap).trans (Category.assoc _ _ _)
    _ = P.left.δ i ≫ (component n H n le_rfl ≫ Q.left.map g.op) := by rw [hgH]
    _ = (P.left.δ i ≫ component n H n le_rfl) ≫ Q.left.map g.op :=
      (Category.assoc _ _ _).symm
    _ = (degreeMap s n H hQ ≫ Q.left.δ i) ≫ Q.left.map g.op := by rw [degreeMap_faces]
    _ = degreeMap s n H hQ ≫ Q.left.map θ :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => degreeMap s n H hQ ≫ a)
          ((Q.left.map_comp (SimplexCategory.δ i).op g.op).symm.trans (congrArg Q.left.map hθ)))

private theorem endomorphism_new (θ : op ⦋n + 1⦌ ⟶ op ⦋n + 1⦌) :
    P.left.map θ ≫ degreeMap s n H hQ = degreeMap s n H hQ ≫ Q.left.map θ := by
  let e := factorThruImage θ.unop
  let j := image.ι θ.unop
  have hdle : (image θ.unop).len ≤ n + 1 := SimplexCategory.len_le_of_mono j
  by_cases hd : (image θ.unop).len ≤ n
  · have hθ : j.op ≫ e.op = θ := by
      apply Quiver.Hom.unop_inj
      simp [e, j]
    have hj := outgoing s n H hQ (image θ.unop).len hd j.op
    have he := degreeMap_epi_naturality s n H hQ (image θ.unop).len hd e.op
    rw [← hθ, P.left.map_comp, Q.left.map_comp]
    simp only [Category.assoc]
    rw [he, ← Category.assoc, hj]
    simp only [Category.assoc]
  · have hlen : (image θ.unop).len = n + 1 := by omega
    let _ : IsIso e := (SimplexCategory.isIso_iff_of_epi e).2 (by simpa [e] using hlen.symm)
    let _ : IsIso j := (SimplexCategory.isIso_iff_of_mono j).2 (by simpa [j] using hlen)
    let _ : IsIso θ.unop := by
      rw [← image.fac θ.unop]
      infer_instance
    have hθ : θ = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      simpa using SimplexCategory.eq_id_of_isIso θ.unop
    subst θ
    simp

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. In degree n+1 use the new whole-degree lift; in
each degree m≤n retain Hₘ. These define the successor components Pₘ→Qₘ for m≤n+1. -/
def newComponent (m : ℕ) (hm : m ≤ n + 1) :
    P.left.obj (op ⦋m⦌) ⟶ Q.left.obj (op ⦋m⦌) := by
  classical
  exact if he : m = n + 1 then
    eqToHom (congrArg (fun l => P.left.obj (op ⦋l⦌)) he) ≫ degreeMap s n H hQ ≫
      eqToHom (congrArg (fun l => Q.left.obj (op ⦋l⦌)) he.symm)
  else
    component n H m (by omega)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. The degree-n+1 successor component is the
polynomial split-degree lift vₙ₊₁. -/
@[simp]
theorem newComponent_new : newComponent s n H hQ (n + 1) le_rfl = degreeMap s n H hQ := by
  simp [newComponent]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. In every degree m≤n the successor component is
exactly Hₘ. -/
@[simp]
theorem newComponent_old (m : ℕ) (hm : m ≤ n) (hm' : m ≤ n + 1) :
    newComponent s n H hQ m hm' = component n H m hm := by
  have hne : m ≠ n + 1 := by omega
  simp [newComponent, hne]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. For m,l≤n+1 and every θ:op[m]→op[l],
P(θ)≫uₗ=uₘ≫Q(θ) for the successor components u. -/
theorem newComponent_naturality {m l : ℕ} (hm : m ≤ n + 1) (hl : l ≤ n + 1)
    (θ : op ⦋m⦌ ⟶ op ⦋l⦌) :
    P.left.map θ ≫ newComponent s n H hQ l hl = newComponent s n H hQ m hm ≫ Q.left.map θ := by
  by_cases hmold : m ≤ n
  · by_cases hlold : l ≤ n
    · rw [newComponent_old s n H hQ l hlold hl, newComponent_old s n H hQ m hmold hm]
      exact component_naturality n H hmold hlold θ
    · have hleq : l = n + 1 := by omega
      subst l
      rw [newComponent_new, newComponent_old s n H hQ m hmold hm]
      exact incoming s n H hQ m hmold θ
  · have hmeq : m = n + 1 := by omega
    subst m
    by_cases hlold : l ≤ n
    · rw [newComponent_new, newComponent_old s n H hQ l hlold hl]
      exact outgoing s n H hQ l hlold θ
    · have hleq : l = n + 1 := by omega
      subst l
      rw [newComponent_new s n H hQ]
      exact endomorphism_new s n H hQ θ

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. Each successor component uₘ satisfies uₘ≫εQₘ=εPₘ. -/
theorem newComponent_augmentation (m : ℕ) (hm : m ≤ n + 1) :
    newComponent s n H hQ m hm ≫ Q.hom.app (op ⦋m⦌) = P.hom.app (op ⦋m⦌) := by
  by_cases hmold : m ≤ n
  · rw [newComponent_old s n H hQ m hmold hm]
    exact component_augmentation n H m hmold
  · have hmeq : m = n + 1 := by omega
    subst m
    rw [newComponent_new]
    exact degreeMap_augmentation s n H hQ

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. The successor components form an augmented
simplicial comparison truncated through n+1. -/
def extend : TruncatedComparison k A P Q (n + 1) :=
  Over.homMk
    { app Δ := newComponent s n H hQ Δ.unop.obj.len Δ.unop.property
      naturality {Δ Δ'} θ :=
        newComponent_naturality s n H hQ Δ.unop.property Δ'.unop.property θ.unop.hom.op }
    (by
      apply NatTrans.ext
      funext Δ
      exact newComponent_augmentation s n H hQ Δ.unop.obj.len Δ.unop.property)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. Restricting the successor comparison back to
degrees at most n gives H as a whole augmented-diagram morphism. -/
theorem extend_restrict :
    (Over.post (SimplicialObject.Truncated.trunc (CommAlgCat.{max u v} k) (n + 1) n)).map
      (extend s n H hQ) = H := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Δ
  exact newComponent_old s n H hQ Δ.unop.obj.len Δ.unop.property
    (Nat.le_trans Δ.unop.property (Nat.le_succ n))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, H a comparison truncated through n, and assume that Q's normalized
additive augmentation is a quasi-isomorphism. The degree-n+1 component of the successor
truncated comparison is the constructed split-degree map vₙ₊₁. -/
theorem extend_new_component :
    component (n + 1) (extend s n H hQ) (n + 1) le_rfl = degreeMap s n H hQ :=
  newComponent_new s n H hQ

end CommAlgCat.PolynomialSplitTruncatedComparison

end
