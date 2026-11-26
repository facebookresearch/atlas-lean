/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

/-
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse

Outer-cutoff totals identified with extended columns over a general abelian
target.

Provides the degreewise isomorphism `outerCutoffTotalXIsoFinite` and lifts it to the
chain-level isomorphism `outerCutoffTotalIsoFinite`, with forward
naturality `outerCutoffTotalFwdCommFinite`.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantBicomplexTail
public import MathlibExt.Algebra.Homology.TotalComplexUpNat
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
@[expose] public section

open CategoryTheory Category Limits

universe u v

namespace FirstQuadrantTail

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For a bicomplex K in an abelian category C with both
differentials raising nonnegative degrees, the cutoff at r is
B^(r)_(p,q)=K_(p,r) when q=r and zero otherwise.
Its inner differential is zero, and its outer differential is
the restriction of the outer differential of K to inner degree r. -/
noncomputable abbrev outerCutoffTotalBicomplexFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  outerCutoff K r

@[simp]
lemma outerCutoffTotalBicomplexFinite_eq_outerCutoff
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) : outerCutoffTotalBicomplexFinite K r = outerCutoff K r :=
  rfl

/-- For a bicomplex K with both cohomological indices in ℕ
in an abelian category C, the slice D_r has degree-p object
K_(p,r) and differential (K.d_(p,p+1))_r.
It is the rth outer complex of the flipped bicomplex. -/
noncomputable abbrev outerCutoffColumnFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) : HomologicalComplex C (ComplexShape.up ℕ) :=
  K.flip.X r

/-- For r ∈ ℕ, the cochain-shape embedding t_r : ℕ → ℕ
is p ↦ p+r. It places outer degree p of a fixed inner-degree-r
slice in total degree p+r and preserves degree-raising differentials. -/
noncomputable abbrev outerCutoffColumnEmbeddingFinite (r : ℕ) :
    (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  tailEmbedding r

/-- For a bicomplex K in an abelian category C with both
differentials raising nonnegative degrees, extend the slice
D_r=(p ↦ K_(p,r)) along p ↦ p+r.
The resulting complex has term K_(n−r,r) for n≥r and a zero
object for n<r, with the inherited outer differential. -/
noncomputable abbrev outerCutoffColumnExtFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) : HomologicalComplex C (ComplexShape.up ℕ) :=
  (outerCutoffColumnFinite K r).extend (outerCutoffColumnEmbeddingFinite r)


-- Compatibility instance; finite-fiber totalization now supplies it automatically.
instance outerCutoffHasTotalFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) : (outerCutoff (C := C) K r).HasTotal (ComplexShape.up ℕ) :=
  inferInstanceAs ((outerCutoffTotalBicomplexFinite K r).HasTotal (ComplexShape.up ℕ))

@[simp]
lemma outerCutoffTotalBicomplexFinite_X
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p : ℕ) :
    (outerCutoffTotalBicomplexFinite K r).X p =
      (HomologicalComplex.single C (ComplexShape.up ℕ) r).obj ((K.X p).X r) :=
  rfl

lemma outerCutoffTotalBicomplexFinite_d
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p p' : ℕ) :
    (outerCutoffTotalBicomplexFinite K r).d p p' =
      (HomologicalComplex.single C (ComplexShape.up ℕ) r).map
        ((K.d p p').f r) :=
  rfl

lemma outerCutoffTotalBicomplexFinite_inner_d
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p q q' : ℕ) : ((outerCutoffTotalBicomplexFinite K r).X p).d q q' = 0 :=
  rfl

lemma outerCutoffColumnFinite_X
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p : ℕ) : (outerCutoffColumnFinite K r).X p = (K.X p).X r :=
  rfl

lemma outerCutoffColumnFinite_d
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p p' : ℕ) : (outerCutoffColumnFinite K r).d p p' = (K.d p p').f r :=
  rfl

lemma outerCutoffColumnEmbeddingFinite_f (r p : ℕ) :
    (outerCutoffColumnEmbeddingFinite r).f p = p + r :=
  rfl

lemma outerCutoffTotalFinite_pi (p q : ℕ) :
    ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = p + q :=
  rfl

/-- For a cohomological bicomplex K in an abelian category,
q=r identifies the cutoff object B^(r)_(p,q) with K_(p,r).
This is the single nonzero inner-degree branch at outer degree p. -/
noncomputable def outerCutoffTotalSingleBranchFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p q : ℕ) (hqr : q = r) :
    ((outerCutoffTotalBicomplexFinite K r).X p).X q ≅ (K.X p).X r :=
  HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) r ((K.X p).X r) q hqr

/-- For a cohomological bicomplex K in an abelian category and
r,p ≥ 0, the retained object B^(r)_(p,r) is canonically isomorphic
to K_(p,r). It is the diagonal branch of the inner-degree-r cutoff. -/
noncomputable def outerCutoffTotalSingleSelfFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p : ℕ) : ((outerCutoffTotalBicomplexFinite K r).X p).X r ≅ (K.X p).X r :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r ((K.X p).X r)

/-- For a cohomological bicomplex K in an abelian category,
specializing the branch identification B^(r)_(p,q) ≅ K_(p,r)
to q=r gives the diagonal identification B^(r)_(p,r) ≅ K_(p,r).
The two canonical maps agree. -/
lemma outerCutoffTotalSingleBranchFinite_rfl
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p : ℕ) :
    outerCutoffTotalSingleBranchFinite K r p r rfl =
      outerCutoffTotalSingleSelfFinite K r p :=
  rfl

/-- For a cohomological bicomplex K in an abelian category and
n=p+r, the extended slice satisfies
(extend_(t_r) D_r)_n ≅ (D_r)_p = K_(p,r).
This is the supported-degree identification for the translation
t_r(p)=p+r. -/
noncomputable def outerCutoffColumnExtBranchFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p n : ℕ) (h : p + r = n) :
    (outerCutoffColumnExtFinite K r).X n ≅ (outerCutoffColumnFinite K r).X p :=
  HomologicalComplex.extendXIso _ _ (by rw [outerCutoffColumnEmbeddingFinite_f]; exact h)

/-- For a cohomological bicomplex K in an abelian category and
p+q=n, the comparison B^(r)_(p,q) → (extend_(t_r)D_r)_n
is zero if q≠r. If q=r, it identifies the source with K_(p,r)
and uses the inverse supported-degree identification n=p+r
to enter the extended slice. -/
noncomputable def outerCutoffTotalSummandMapFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = n) :
    ((outerCutoffTotalBicomplexFinite K r).X p).X q ⟶
      (outerCutoffColumnExtFinite K r).X n :=
  if hqr : q = r then
    (outerCutoffTotalSingleBranchFinite K r p q hqr).hom ≫
      (outerCutoffColumnExtBranchFinite K r p n
        (by subst hqr; simpa [outerCutoffTotalFinite_pi] using h)).inv
  else 0

/-- For a cohomological bicomplex K in an abelian category,
the forward comparison F_n : Tot(B^(r))_n → (extend_(t_r)D_r)_n
is the coproduct map whose only retained summand has q=r.
It identifies the (p,r) branch in total degree p+r with the
translated slice term. -/
noncomputable def outerCutoffTotalFwdFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) :
    ((outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ)).X n ⟶
      (outerCutoffColumnExtFinite K r).X n :=
  (outerCutoffTotalBicomplexFinite K r).totalDesc
    (outerCutoffTotalSummandMapFinite K r n)

@[simp]
lemma outerCutoffTotalIotaFwdFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = n) :
    (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p q n h ≫
        outerCutoffTotalFwdFinite K r n =
      outerCutoffTotalSummandMapFinite K r n p q h :=
  (outerCutoffTotalBicomplexFinite K r).ι_totalDesc
    (outerCutoffTotalSummandMapFinite K r n) p q h

open Classical in
/-- For a cohomological bicomplex K in an abelian category,
the backward comparison B_n : (extend_(t_r)D_r)_n → Tot(B^(r))_n
uses the unique p with n=p+r when n≥r, identifies the term with
K_(p,r), and includes its retained total summand.
For n<r it is the zero map from a zero extension object. -/
noncomputable def outerCutoffTotalBwdFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) :
    (outerCutoffColumnExtFinite K r).X n ⟶
      ((outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ)).X n :=
  if h : ∃ p, (outerCutoffColumnEmbeddingFinite r).f p = n then
    (outerCutoffColumnExtBranchFinite K r h.choose n (by
      have hc := h.choose_spec
      rw [outerCutoffColumnEmbeddingFinite_f] at hc; exact hc)).hom ≫
      (outerCutoffTotalSingleSelfFinite K r h.choose).inv ≫
      (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) h.choose r n (by
        have hc : h.choose + r = n := by
          have hh := h.choose_spec
          rw [outerCutoffColumnEmbeddingFinite_f] at hh; exact hh
        simpa [outerCutoffTotalFinite_pi] using hc)
  else 0

/-- For a cohomological bicomplex K in an abelian category and
p+q=n, if q≠r then the inclusion B^(r)_(p,q) → Tot(B^(r))_n
is zero. Its source is the zero object of the off-slice branch. -/
lemma outerCutoffTotalIotaOffRowFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = n) (hqr : q ≠ r) :
    (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p q n h = 0 := by
  have hz : IsZero (((outerCutoffTotalBicomplexFinite K r).X p).X q) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hqr
  exact hz.eq_of_src _ _

/-- For a cohomological bicomplex K in an abelian category and
n=p+r, the forward summand map identifies B^(r)_(p,r) with
K_(p,r), then uses the inverse identification
(extend_(t_r)D_r)_n ≅ K_(p,r).
Thus it retains the single supported slice branch without an
additional scalar sign. -/
lemma outerCutoffTotalSummandOnRowFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n p : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, r) = n) :
    outerCutoffTotalSummandMapFinite K r n p r h =
      (outerCutoffTotalSingleSelfFinite K r p).hom ≫
        (outerCutoffColumnExtBranchFinite K r p n
          (by simpa [outerCutoffTotalFinite_pi] using h)).inv := by
  unfold outerCutoffTotalSummandMapFinite
  rw [dite_eq_left rfl, outerCutoffTotalSingleBranchFinite_rfl]

lemma outerCutoffTotalSummandOffRowFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = n) (hqr : q ≠ r) :
    outerCutoffTotalSummandMapFinite K r n p q h = 0 := by
  simp only [outerCutoffTotalSummandMapFinite, dite_eq_right hqr]

/-- For a cohomological bicomplex K in an abelian category,
if no p ∈ ℕ satisfies p+r=n, then (extend_(t_r)D_r)_n is a zero
object. Equivalently, the extended slice is zero for n<r. -/
lemma outerCutoffColumnExtOffImageFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) (h : ¬ ∃ p, (outerCutoffColumnEmbeddingFinite r).f p = n) :
    IsZero ((outerCutoffColumnExtFinite K r).X n) :=
  (outerCutoffColumnFinite K r).isZero_extend_X
    (outerCutoffColumnEmbeddingFinite r) n
    (fun i hi => h ⟨i, hi⟩)

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- For a cohomological bicomplex K in an abelian category,
the degreewise comparisons F_n : Tot(B^(r))_n → (extend D_r)_n
and B_n in the reverse direction satisfy
B_n ∘ F_n = id_(Tot(B^(r))_n).
Only the retained q=r branch contributes. -/
theorem outerCutoffTotalFwdBwdIdFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) :
    outerCutoffTotalFwdFinite K r n ≫ outerCutoffTotalBwdFinite K r n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [← Category.assoc, outerCutoffTotalIotaFwdFinite]
  by_cases hqr : q = r
  · subst q
    have hpr : p + r = n := by simpa [outerCutoffTotalFinite_pi] using hpq
    have hex : ∃ s, (outerCutoffColumnEmbeddingFinite r).f s = n :=
      ⟨p, by rw [outerCutoffColumnEmbeddingFinite_f]; exact hpr⟩
    have hcp : hex.choose = p :=
      (outerCutoffColumnEmbeddingFinite r).injective_f
        (hex.choose_spec.trans (by rw [outerCutoffColumnEmbeddingFinite_f]; exact hpr.symm))
    subst hcp
    have hbwd : outerCutoffTotalBwdFinite K r n =
        (outerCutoffColumnExtBranchFinite K r hex.choose n
          (by simpa [outerCutoffTotalFinite_pi] using hpq)).hom ≫
          (outerCutoffTotalSingleSelfFinite K r hex.choose).inv ≫
          (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ)
            hex.choose r n hpq := by
      unfold outerCutoffTotalBwdFinite
      rw [dite_eq_left hex]
    rw [outerCutoffTotalSummandOnRowFinite K r n hex.choose hpq, hbwd]
    have hE : ∀ (h1 h2 : hex.choose + r = n),
        (outerCutoffColumnExtBranchFinite K r hex.choose n h1).inv ≫
          (outerCutoffColumnExtBranchFinite K r hex.choose n h2).hom = 𝟙 _ := by
      intro h1 h2
      rw [proof_irrel h1 h2]
      exact Iso.inv_hom_id _
    simp only [Category.assoc]
    rw [← Category.assoc
      (outerCutoffColumnExtBranchFinite K r hex.choose n _).inv
      (outerCutoffColumnExtBranchFinite K r hex.choose n _).hom _,
      hE _ _, Category.id_comp,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rw [outerCutoffTotalSummandOffRowFinite K r n p q hpq hqr, zero_comp,
      outerCutoffTotalIotaOffRowFinite K r n p q hpq hqr, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- For a cohomological bicomplex K in an abelian category,
the degreewise cutoff-total and extension comparisons satisfy
F_n ∘ B_n = id_((extend_(t_r)D_r)_n).
In unsupported degrees n<r both extension and total terms are
zero objects. -/
theorem outerCutoffTotalBwdFwdIdFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) :
    outerCutoffTotalBwdFinite K r n ≫ outerCutoffTotalFwdFinite K r n = 𝟙 _ := by
  by_cases hex : ∃ p, (outerCutoffColumnEmbeddingFinite r).f p = n
  · set p := hex.choose with hpdef
    have hp : (outerCutoffColumnEmbeddingFinite r).f p = n := by
      rw [hpdef]; exact hex.choose_spec
    have hpr : p + r = n := by rw [outerCutoffColumnEmbeddingFinite_f] at hp; exact hp
    have hpq : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (p, r) = n := by
      simpa [outerCutoffTotalFinite_pi] using hpr
    have hbwd : outerCutoffTotalBwdFinite K r n =
        (outerCutoffColumnExtBranchFinite K r p n hpr).hom ≫
          (outerCutoffTotalSingleSelfFinite K r p).inv ≫
          (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r n hpq := by
      unfold outerCutoffTotalBwdFinite
      rw [dite_eq_left hex]
    rw [hbwd, Category.assoc, Category.assoc, outerCutoffTotalIotaFwdFinite,
      outerCutoffTotalSummandOnRowFinite]
    have hE : ∀ (h1 h2 : p + r = n),
        (outerCutoffColumnExtBranchFinite K r p n h1).hom ≫
          (outerCutoffColumnExtBranchFinite K r p n h2).inv = 𝟙 _ := by
      intro h1 h2
      rw [proof_irrel h1 h2]
      exact Iso.hom_inv_id _
    rw [← Category.assoc (outerCutoffTotalSingleSelfFinite K r p).inv
      (outerCutoffTotalSingleSelfFinite K r p).hom _,
      Iso.inv_hom_id, Category.id_comp]
    exact hE _ _
  · have hbwd : outerCutoffTotalBwdFinite K r n = 0 := by
      unfold outerCutoffTotalBwdFinite; rw [dite_eq_right hex]
    rw [hbwd, zero_comp]
    exact (outerCutoffColumnExtOffImageFinite K r n hex).eq_of_src _ _

/-- For a cohomological bicomplex K in an abelian category and
r,n ≥ 0, there is an isomorphism
Tot(B^(r))_n ≅ (extend_(t_r)D_r)_n.
Its forward map retains the inner-degree-r total branch, and
its inverse includes that branch at the unique degree n=p+r. -/
noncomputable def outerCutoffTotalXIsoFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) :
    ((outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ)).X n ≅
      (((K.flip.X r).extend (tailEmbedding r)).X n) where
  hom := outerCutoffTotalFwdFinite K r n
  inv := outerCutoffTotalBwdFinite K r n
  hom_inv_id := outerCutoffTotalFwdBwdIdFinite K r n
  inv_hom_id := outerCutoffTotalBwdFwdIdFinite K r n

/-- For a cohomological bicomplex K in an abelian category,
the forward degree-(p+r) isomorphism composed with the
(p,r) total inclusion is the canonical map
B^(r)_(p,r) ≅ K_(p,r) ≅ (extend_(t_r)D_r)_(p+r).
This is its retained-summand formula. -/
lemma outerCutoffTotalXIsoHomIotaFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r p : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, r) = p + r) :
    (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r (p + r) h ≫
        (outerCutoffTotalXIsoFinite K r (p + r)).hom =
      (outerCutoffTotalSingleSelfFinite K r p).hom ≫
        (outerCutoffColumnExtBranchFinite K r p (p + r) h).inv := by
  change _ ≫ outerCutoffTotalFwdFinite K r (p + r) = _
  rw [outerCutoffTotalIotaFwdFinite, outerCutoffTotalSummandOnRowFinite]

set_option backward.isDefEq.respectTransparency false in
/-- For a cohomological bicomplex K in an abelian category,
the composition of any cutoff total summand inclusion with the
inner total-differential component D₂ is zero.
The cutoff B^(r) has zero inner differential, so this holds in
every pair of total degrees. -/
theorem outerCutoffIotaD2Finite_eq_zero
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r i j p q : ℕ)
    (hpq : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = i) :
    (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p q i hpq ≫
      (outerCutoffTotalBicomplexFinite K r).D₂ (ComplexShape.up ℕ) i j = 0 := by
  rw [HomologicalComplex₂.ι_D₂]
  unfold HomologicalComplex₂.d₂
  rw [outerCutoffTotalBicomplexFinite_inner_d]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- For a cohomological bicomplex K in an abelian category,
on the retained branch (p,r) with i=p+r and j=i+1, the outer
total-differential component followed by F_j equals F_i followed
by the differential of extend_(t_r)D_r.
The latter is the translated outer slice differential. -/
theorem outerCutoffIotaD1FwdOnRowFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r i j p : ℕ)
    (hpq : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, r) = i)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
      (outerCutoffTotalBicomplexFinite K r).D₁ (ComplexShape.up ℕ) i j ≫
        outerCutoffTotalFwdFinite K r j =
    (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
      outerCutoffTotalFwdFinite K r i ≫ (outerCutoffColumnExtFinite K r).d i j := by
  have hpr : p + r = i := by simpa [outerCutoffTotalFinite_pi] using hpq
  have hij' : i + 1 = j := hij
  have hnext : p + 1 + r = j := by omega
  have hpq' : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p + 1, r) = j := by
    simpa [outerCutoffTotalFinite_pi] using hnext
  have hpp1 : (ComplexShape.up ℕ).Rel p (p + 1) :=
    ComplexShape.up_mk p (p + 1) rfl
  have hI : (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
      (outerCutoffTotalBicomplexFinite K r).D₁ (ComplexShape.up ℕ) i j =
      (outerCutoffTotalBicomplexFinite K r).d₁ (ComplexShape.up ℕ) p r j :=
    (outerCutoffTotalBicomplexFinite K r).ι_D₁ (ComplexShape.up ℕ) i j p r hpq
  have hD : (outerCutoffTotalBicomplexFinite K r).d₁ (ComplexShape.up ℕ) p r j =
      ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (p, r) •
        (((outerCutoffTotalBicomplexFinite K r).d p (p + 1)).f r ≫
          (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ)
            (p + 1) r j hpq') :=
    (outerCutoffTotalBicomplexFinite K r).d₁_eq (ComplexShape.up ℕ) hpp1 r j hpq'
  have hTd : ((outerCutoffTotalBicomplexFinite K r).d p (p + 1)).f r =
      (outerCutoffTotalSingleSelfFinite K r p).hom ≫ ((K.d p (p + 1)).f r) ≫
        (outerCutoffTotalSingleSelfFinite K r (p + 1)).inv := by
    rw [outerCutoffTotalBicomplexFinite_d, HomologicalComplex.single_map_f_self]
    rfl
  have hFwdJ := outerCutoffTotalIotaFwdFinite K r j (p + 1) r hpq'
  have hSumJ := outerCutoffTotalSummandOnRowFinite K r j (p + 1) hpq'
  have hFwdI := outerCutoffTotalIotaFwdFinite K r i p r hpq
  have hSumI := outerCutoffTotalSummandOnRowFinite K r i p hpq
  have hi0 : (outerCutoffColumnEmbeddingFinite r).f p = i := by
    rw [outerCutoffColumnEmbeddingFinite_f]; exact hpr
  have hj0 : (outerCutoffColumnEmbeddingFinite r).f (p + 1) = j := by
    rw [outerCutoffColumnEmbeddingFinite_f]; exact hnext
  have hExt := HomologicalComplex.extend_d_eq (outerCutoffColumnFinite K r)
    (outerCutoffColumnEmbeddingFinite r) hi0 hj0
  have hCold : (outerCutoffColumnFinite K r).d p (p + 1) = (K.d p (p + 1)).f r :=
    outerCutoffColumnFinite_d K r p (p + 1)
  have hBrX : ∀ (a n : ℕ) (h : a + r = n)
      (hh : (outerCutoffColumnEmbeddingFinite r).f a = n),
      outerCutoffColumnExtBranchFinite K r a n h =
        HomologicalComplex.extendXIso (outerCutoffColumnFinite K r)
          (outerCutoffColumnEmbeddingFinite r) hh := by
    intro a n h hh
    unfold outerCutoffColumnExtBranchFinite
    exact congrArg _ (proof_irrel _ _)
  have hEps : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, r) = 1 := rfl
  have hL : (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
        (outerCutoffTotalBicomplexFinite K r).D₁ (ComplexShape.up ℕ) i j ≫
          outerCutoffTotalFwdFinite K r j =
      (outerCutoffTotalBicomplexFinite K r).d₁ (ComplexShape.up ℕ) p r j ≫
        outerCutoffTotalFwdFinite K r j := by
    rw [← Category.assoc, hI]
  have hR : (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
        outerCutoffTotalFwdFinite K r i ≫ (outerCutoffColumnExtFinite K r).d i j =
      outerCutoffTotalSummandMapFinite K r i p r hpq ≫
        (outerCutoffColumnExtFinite K r).d i j := by
    rw [← Category.assoc, hFwdI]
  rw [hL, hD, Linear.units_smul_comp, hEps, one_smul]
  have eJ : ((((outerCutoffTotalBicomplexFinite K r).d p (p + 1)).f r ≫
        (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ)
          (p + 1) r j hpq') ≫
        outerCutoffTotalFwdFinite K r j) =
      ((outerCutoffTotalBicomplexFinite K r).d p (p + 1)).f r ≫
        ((outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ)
          (p + 1) r j hpq' ≫
          outerCutoffTotalFwdFinite K r j) := Category.assoc _ _ _
  rw [eJ, hFwdJ, hSumJ, hTd, hR, hSumI, hExt, hCold]
  simp only [Category.assoc]
  rw [hBrX _ _ _ hj0, hBrX _ _ _ hi0]
  rw [← Category.assoc (outerCutoffTotalSingleSelfFinite K r (p + 1)).inv _ _,
    Iso.inv_hom_id, Category.id_comp,
    ← Category.assoc (HomologicalComplex.extendXIso (outerCutoffColumnFinite K r)
      (outerCutoffColumnEmbeddingFinite r) hi0).inv _ _,
    Iso.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- For a cohomological bicomplex K in an abelian category
and j=i+1, the forward comparisons satisfy
d_(extend D_r)^(i,j) ∘ F_i = F_j ∘ d_(Tot B^(r))^(i,j).
Thus the retained-branch degree maps form a cochain map. -/
theorem outerCutoffTotalFwdCommFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    outerCutoffTotalFwdFinite K r i ≫ (outerCutoffColumnExtFinite K r).d i j =
      ((outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ)).d i j ≫
        outerCutoffTotalFwdFinite K r j := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  by_cases hqr : q = r
  · subst q
    have hL : (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
          (outerCutoffTotalFwdFinite K r i ≫ (outerCutoffColumnExtFinite K r).d i j) =
        ((outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
          outerCutoffTotalFwdFinite K r i) ≫ (outerCutoffColumnExtFinite K r).d i j :=
      (Category.assoc _ _ _).symm
    have hR : (outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
          (((outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ)).d i j ≫
            outerCutoffTotalFwdFinite K r j) =
        ((outerCutoffTotalBicomplexFinite K r).ιTotal (ComplexShape.up ℕ) p r i hpq ≫
          ((outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ)).d i j) ≫
          outerCutoffTotalFwdFinite K r j :=
      (Category.assoc _ _ _).symm
    rw [hL, hR, HomologicalComplex₂.total_d, Preadditive.comp_add,
      outerCutoffIotaD2Finite_eq_zero K r i j p r hpq, Preadditive.add_comp,
      Limits.zero_comp, add_zero]
    simpa only [Category.assoc] using
      (outerCutoffIotaD1FwdOnRowFinite K r i j p hpq hij).symm
  · have hz : Limits.IsZero (((outerCutoffTotalBicomplexFinite K r).X p).X q) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hqr
    exact hz.eq_of_src _ _

/-- For a bicomplex K in an abelian category C with both
differentials raising nonnegative degrees, there is a cochain
isomorphism Tot(B^(r)) ≅ extend_(p↦p+r)(K.flip_r).
It identifies the sole inner-degree-r branch in each total
antidiagonal and retains the outer differential.
The category object and morphism universes are independent. -/
noncomputable def outerCutoffTotalIsoFinite
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r : ℕ) :
    (outerCutoff (C := C) K r).total (ComplexShape.up ℕ) ≅
      (K.flip.X r).extend (tailEmbedding r) :=
  HomologicalComplex.Hom.isoOfComponents (outerCutoffTotalXIsoFinite K r)
    (fun i j hij => outerCutoffTotalFwdCommFinite K r i j hij)

/-- For a cohomological bicomplex K in an abelian category,
the degree-n component isomorphism of
Tot(B^(r)) ≅ extend_(t_r)D_r is the cutoff-total object comparison
whose forward map retains the q=r branch and whose inverse includes it. -/
lemma outerCutoffTotalIsoFinite_app
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (r n : ℕ) :
    HomologicalComplex.Hom.isoApp (outerCutoffTotalIsoFinite K r) n =
      outerCutoffTotalXIsoFinite K r n :=
  HomologicalComplex.Hom.isoOfComponents_app _ _ _


set_option backward.isDefEq.respectTransparency false in
/-- For a cohomological bicomplex map φ : K → L in an abelian
category, let φ_r : K.flip_r → L.flip_r be its inner-degree-r
slice map. The cutoff-total comparisons satisfy
F_L ∘ Tot(B^(r)(φ)) = extend_(t_r)(φ_r) ∘ F_K.
This is a square of nonnegative cochain complexes. -/
theorem outerCutoffTotalIsoFinite_hom_naturality
    {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (phi : K ⟶ L) (r : ℕ) :
    HomologicalComplex₂.total.map
      ((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map phi)
      (ComplexShape.up ℕ) ≫
      (FirstQuadrantTail.outerCutoffTotalIsoFinite L r).hom =
    (FirstQuadrantTail.outerCutoffTotalIsoFinite K r).hom ≫
      HomologicalComplex.extendMap
        (((HomologicalComplex₂.flipFunctor C
          (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r)
        (FirstQuadrantTail.tailEmbedding r) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hCf1 : ((HomologicalComplex₂.total.map
      ((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map phi)
      (ComplexShape.up ℕ) ≫
      (FirstQuadrantTail.outerCutoffTotalIsoFinite L r).hom).f n) =
      ((HomologicalComplex₂.total.map
        ((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map phi)
        (ComplexShape.up ℕ)).f n ≫
        FirstQuadrantTail.outerCutoffTotalFwdFinite L r n) := rfl
  have hCf2 : (((FirstQuadrantTail.outerCutoffTotalIsoFinite K r).hom ≫
      HomologicalComplex.extendMap
        (((HomologicalComplex₂.flipFunctor C
          (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r)
        (FirstQuadrantTail.tailEmbedding r)).f n) =
      (FirstQuadrantTail.outerCutoffTotalFwdFinite K r n ≫
        (HomologicalComplex.extendMap
          (((HomologicalComplex₂.flipFunctor C
            (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r)
          (FirstQuadrantTail.tailEmbedding r)).f n) := rfl
  rw [hCf1, hCf2, ← Category.assoc]
  have hMap :
      ((((FirstQuadrantTail.outerCutoffFunctor (C := C) r).obj
          K).ιTotal (ComplexShape.up ℕ) p q n hpq) ≫
        (HomologicalComplex₂.total.map
          ((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map phi)
          (ComplexShape.up ℕ)).f n) =
      (((((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map
          phi).f p).f q) ≫
        (((FirstQuadrantTail.outerCutoffFunctor (C := C) r).obj
          L).ιTotal (ComplexShape.up ℕ) p q n hpq)) :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ p q n hpq
  rw [hMap, Category.assoc]
  have hIL : (((((FirstQuadrantTail.outerCutoffFunctor (C := C) r).obj
      L).ιTotal (ComplexShape.up ℕ) p q n hpq) ≫
      FirstQuadrantTail.outerCutoffTotalFwdFinite L r n)) =
      FirstQuadrantTail.outerCutoffTotalSummandMapFinite L r n p q hpq :=
    FirstQuadrantTail.outerCutoffTotalIotaFwdFinite L r n p q hpq
  have hIK : (((((FirstQuadrantTail.outerCutoffFunctor (C := C) r).obj
      K).ιTotal (ComplexShape.up ℕ) p q n hpq) ≫
      FirstQuadrantTail.outerCutoffTotalFwdFinite K r n)) =
      FirstQuadrantTail.outerCutoffTotalSummandMapFinite K r n p q hpq :=
    FirstQuadrantTail.outerCutoffTotalIotaFwdFinite K r n p q hpq
  rw [hIL, ← Category.assoc, hIK]
  by_cases hqr : q = r
  · subst q
    have hpr : p + r = n := hpq
    have hem : (FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r).f p = n := hpr
    have hOnL : FirstQuadrantTail.outerCutoffTotalSummandMapFinite L r n p r hpq =
        ((FirstQuadrantTail.outerCutoffTotalSingleSelfFinite L r p).hom ≫
          (FirstQuadrantTail.outerCutoffColumnExtBranchFinite L r p n hpr).inv) :=
      FirstQuadrantTail.outerCutoffTotalSummandOnRowFinite L r n p hpq
    have hOnK : FirstQuadrantTail.outerCutoffTotalSummandMapFinite K r n p r hpq =
        ((FirstQuadrantTail.outerCutoffTotalSingleSelfFinite K r p).hom ≫
          (FirstQuadrantTail.outerCutoffColumnExtBranchFinite K r p n hpr).inv) :=
      FirstQuadrantTail.outerCutoffTotalSummandOnRowFinite K r n p hpq
    rw [hOnL, hOnK]
    have hF0 : (((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map
        phi).f p) =
        ((FirstQuadrantTail.cutoffLayerFunctor (C := C) r).map
          (phi.f p)) := rfl
    have hF : ((((FirstQuadrantTail.outerCutoffFunctor (C := C) r).map
        phi).f p).f r) =
        ((FirstQuadrantTail.outerCutoffTotalSingleSelfFinite K r p).hom ≫
          ((phi.f p).f r) ≫
          (FirstQuadrantTail.outerCutoffTotalSingleSelfFinite L r p).inv) := by
      rw [hF0, FirstQuadrantTail.cutoffLayerFunctor_map,
        HomologicalComplex.single_map_f_self]
      rfl
    let psi : FirstQuadrantTail.outerCutoffColumnFinite K r ⟶
        FirstQuadrantTail.outerCutoffColumnFinite L r :=
      (((HomologicalComplex₂.flipFunctor C
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r)
    have hG : psi.f p = ((phi.f p).f r) := rfl
    have hBrK : HomologicalComplex.extendXIso
        (FirstQuadrantTail.outerCutoffColumnFinite K r)
        (FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r) hem =
        FirstQuadrantTail.outerCutoffColumnExtBranchFinite K r p n hpr := by rfl
    have hBrL : HomologicalComplex.extendXIso
        (FirstQuadrantTail.outerCutoffColumnFinite L r)
        (FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r) hem =
        FirstQuadrantTail.outerCutoffColumnExtBranchFinite L r p n hpr := by rfl
    have hE : ((HomologicalComplex.extendMap
        psi
        (FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r)).f n) =
        ((FirstQuadrantTail.outerCutoffColumnExtBranchFinite K r p n hpr).hom ≫
          psi.f p ≫
          (FirstQuadrantTail.outerCutoffColumnExtBranchFinite L r p n hpr).inv) := by
      rw [HomologicalComplex.extendMap_f (φ := psi)
        (e := FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r) (h := hem),
        hBrK, hBrL]
    have hPsi : ((HomologicalComplex.extendMap
        (((HomologicalComplex₂.flipFunctor C
          (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r)
        (FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r)).f n) =
        ((HomologicalComplex.extendMap
          psi
          (FirstQuadrantTail.outerCutoffColumnEmbeddingFinite r)).f n) := rfl
    rw [hPsi, hF, hE, hG]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · have hOffL : FirstQuadrantTail.outerCutoffTotalSummandMapFinite L r n p q hpq =
        0 :=
      FirstQuadrantTail.outerCutoffTotalSummandOffRowFinite L r n p q hpq hqr
    have hOffK : FirstQuadrantTail.outerCutoffTotalSummandMapFinite K r n p q hpq =
        0 :=
      FirstQuadrantTail.outerCutoffTotalSummandOffRowFinite K r n p q hpq hqr
    rw [hOffL, hOffK]
    simp

/-- For a cohomological bicomplex map φ : K → L in an abelian
category and r ≥ 0, the total map of the inner-degree-r cutoffs
is a quasi-isomorphism if and only if the slice map
φ_r : K.flip_r → L.flip_r is a quasi-isomorphism.
The natural cutoff-total isomorphisms identify the total map
with extension of φ_r along p ↦ p+r. -/
theorem totalOuterCutoffMap_quasiIso_iff_finite
    (K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (phi : K ⟶ L) (r : ℕ) :
    QuasiIso (HomologicalComplex₂.total.map
      ((outerCutoffFunctor (C := C) r).map phi)
      (ComplexShape.up ℕ)) ↔
      QuasiIso (((HomologicalComplex₂.flipFunctor C
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r) := by
  let f : (outerCutoffTotalBicomplexFinite K r).total (ComplexShape.up ℕ) ⟶
      (outerCutoffTotalBicomplexFinite L r).total (ComplexShape.up ℕ) :=
    HomologicalComplex₂.total.map
      ((outerCutoffFunctor (C := C) r).map phi)
      (ComplexShape.up ℕ)
  let g : outerCutoffColumnExtFinite K r ⟶ outerCutoffColumnExtFinite L r :=
    HomologicalComplex.extendMap
      (((HomologicalComplex₂.flipFunctor C
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r)
      (tailEmbedding r)
  let e : Arrow.mk f ≅ Arrow.mk g :=
    Arrow.isoMk (outerCutoffTotalIsoFinite K r) (outerCutoffTotalIsoFinite L r)
      (outerCutoffTotalIsoFinite_hom_naturality phi r).symm
  calc QuasiIso f ↔ QuasiIso g := quasiIso_iff_of_arrow_mk_iso f g e
    _ ↔ QuasiIso (((HomologicalComplex₂.flipFunctor C
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map phi).f r) :=
      HomologicalComplex.quasiIso_extendMap_iff _ _

end FirstQuadrantTail

end
