/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Embedding.RestrictionExtendAdjunction
public import MathlibExt.Algebra.Homology.Embedding.NatInitialInterval
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncMap
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Finite initial cotruncations of nonnegative cochain complexes

Let C be a category with zero morphisms and a zero object. Cotruncation at
q of a nonnegative cochain complex K retains its terms and differentials
in degrees 0 through q and extends by zero above q. The retained top term
is Kᑫ. There is a natural projection π_q:K → Cot_q(K).

For p≤q, the transition Cot_q(K) → Cot_p(K) is the identity in retained
coordinates and satisfies π_p=t_qp ∘ π_q. These transitions are natural
in K, compose for p≤q≤r, and give an inverse system indexed by ℕᵒᵖ.
Restriction to [0,q] and extension by zero give the corresponding Hom-set
equivalence for targets supported in this initial interval.

If C is abelian, π_q induces a cohomology isomorphism in every degree n<q,
natural in cochain maps. This comparison is strictly below the cutoff.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape.NatInitialInterval

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C]

section Maps

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- For a category C with zero morphisms and a zero object, a nonnegative
cochain complex K and q∈ℕ, the complex Cot_q(K) obtained by restricting
K to the initial degrees [0,q] and extending by zero above q. Its top
retained term is Kᑫ and its differential out of that term is zero. -/
abbrev finiteCotruncation (K : CochainComplex C ℕ) (q : ℕ) : CochainComplex C ℕ :=
  K.stupidTrunc (upEmbedding q)

/-- Let C have zero morphisms and a zero object. For a nonnegative cochain
complex K and n≤q, the canonical term isomorphism
eₙ:Cot_q(K)ⁿ ≅ Kⁿ in the retained interval [0,q]. -/
def finiteCotruncationXIso (K : CochainComplex C ℕ) (q n : ℕ) (hn : n ≤ q) :
    (K.finiteCotruncation q).X n ≅ K.X n :=
  K.stupidTruncXIso (upEmbedding q) (i := ⟨n, by omega⟩) rfl

/-- For a nonnegative cochain complex K in a category C with zero morphisms
and a zero object, the n-th term of Cot_q(K) is a zero object whenever q<n. -/
theorem finiteCotruncation_isZero (K : CochainComplex C ℕ) (q n : ℕ) (hn : q < n) :
    IsZero ((K.finiteCotruncation q).X n) :=
  K.isZero_stupidTrunc_X (upEmbedding q) n (by
    intro i hi
    have hmem : n ∈ Set.range (upEmbedding q).f := ⟨i, hi⟩
    have := (upEmbedding_range q n).1 hmem
    omega)

/-- Let C have zero morphisms and a zero object, and let K be a nonnegative
cochain complex. For i,j≤q, write eᵢ:Cot_q(K)ⁱ ≅ Kⁱ and
eⱼ:Cot_q(K)ʲ ≅ Kʲ for the retained-term isomorphisms. The differential
of Cot_q(K) from i to j is eⱼ⁻¹ ∘ d_K(i,j) ∘ eᵢ. -/
theorem finiteCotruncation_d (K : CochainComplex C ℕ) (q i j : ℕ)
    (hi : i ≤ q) (hj : j ≤ q) :
    (K.finiteCotruncation q).d i j =
      (K.finiteCotruncationXIso q i hi).hom ≫ K.d i j ≫
        (K.finiteCotruncationXIso q j hj).inv :=
  K.stupidTrunc_d_eq (upEmbedding q) (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) rfl rfl

/-- For a category C with zero morphisms and a zero object, a cochain map
f:K → L and q∈ℕ, the induced map Cot_q(f):Cot_q(K) → Cot_q(L),
obtained by restricting f to [0,q] and extending by zero. -/
abbrev finiteCotruncationMap {K L : CochainComplex C ℕ} (f : K ⟶ L) (q : ℕ) :
    K.finiteCotruncation q ⟶ L.finiteCotruncation q :=
  HomologicalComplex.stupidTruncMap f (upEmbedding q)

/-- In a category C with zero morphisms and a zero object, cotruncation at
q is the endofunctor of nonnegative cochain complexes that retains
degrees [0,q], extends by zero, and applies the same restriction and
extension to cochain maps. -/
def finiteCotruncationFunctor (q : ℕ) : CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  (upEmbedding q).stupidTruncFunctor C

/-- Let C have zero morphisms and a zero object. For a nonnegative cochain
complex K and q∈ℕ, the canonical projection π_q:K → Cot_q(K) from
restriction to the initial interval [0,q] followed by extension by zero. -/
abbrev πFiniteCotruncation (K : CochainComplex C ℕ) (q : ℕ) :
    K ⟶ K.finiteCotruncation q := K.πStupidTrunc (upEmbedding q)

theorem πFiniteCotruncation_f (K : CochainComplex C ℕ) (q n : ℕ) (hn : n ≤ q) :
    (K.πFiniteCotruncation q).f n = (K.finiteCotruncationXIso q n hn).inv :=
  K.πStupidTrunc_f_eq (upEmbedding q) (p := ⟨n, by omega⟩) rfl

theorem πFiniteCotruncation_f_zero (K : CochainComplex C ℕ) (q n : ℕ) (hn : q < n) :
    (K.πFiniteCotruncation q).f n = 0 :=
  (K.finiteCotruncation_isZero q n hn).eq_of_tgt _ _

/-- For a cochain map f:K → L in a category C with zero morphisms and a
zero object, the projections to the finite cotruncations satisfy
π_q(L) ∘ f = Cot_q(f) ∘ π_q(K). -/
@[reassoc]
theorem πFiniteCotruncation_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) (q : ℕ) :
    f ≫ L.πFiniteCotruncation q =
      K.πFiniteCotruncation q ≫ finiteCotruncationMap f q :=
  (HomologicalComplex.πStupidTrunc_naturality f (upEmbedding q)).symm

/-- Let C have zero morphisms and a zero object, K a nonnegative cochain
complex, and p≤q. Restricting Cot_q(K) to the smaller initial interval
[0,p] gives a complex canonically isomorphic to the restriction of K
to [0,p]. -/
def finiteCotruncationRestrictionIso (K : CochainComplex C ℕ) {p q : ℕ} (hpq : p ≤ q) :
    (K.finiteCotruncation q).restriction (upEmbedding p) ≅
      K.restriction (upEmbedding p) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => K.finiteCotruncationXIso q i.val
      ((Nat.le_of_lt_succ i.isLt).trans hpq))
    (by
      intro i j hij
      have hi : i.val ≤ q := (Nat.le_of_lt_succ i.isLt).trans hpq
      have hj : j.val ≤ q := (Nat.le_of_lt_succ j.isLt).trans hpq
      change (K.finiteCotruncationXIso q i.val hi).hom ≫ K.d i.val j.val =
        (K.finiteCotruncation q).d i.val j.val ≫
          (K.finiteCotruncationXIso q j.val hj).hom
      rw [finiteCotruncation_d K q i.val j.val hi hj]
      let a := (K.finiteCotruncationXIso q i.val hi).hom
      let d := K.d i.val j.val
      let e := K.finiteCotruncationXIso q j.val hj
      change a ≫ d = (a ≫ d ≫ e.inv) ≫ e.hom
      exact ((Category.assoc a (d ≫ e.inv) e.hom).trans
        ((congrArg (fun z => a ≫ z) (Category.assoc d e.inv e.hom)).trans
          ((congrArg (fun z => a ≫ d ≫ z) e.inv_hom_id).trans
            (congrArg (fun z => a ≫ z) (Category.comp_id d))))).symm)

/-- For a nonnegative cochain complex K in a category C with zero morphisms
and a zero object and p≤q, the transition t_qp:Cot_q(K) → Cot_p(K),
obtained from the identification of their restrictions to [0,p] and
extension by zero. -/
def finiteCotruncationTransition (K : CochainComplex C ℕ) {p q : ℕ} (hpq : p ≤ q) :
    K.finiteCotruncation q ⟶ K.finiteCotruncation p :=
  (upEmbedding p).liftExtend (K.finiteCotruncationRestrictionIso hpq).hom
    ((upEmbedding p).hasLift_of_isTruncLE _)

/-- Let C have zero morphisms and a zero object, K a nonnegative cochain
complex, p≤q and n≤p. If e_qn:Cot_q(K)ⁿ ≅ Kⁿ and
e_pn:Cot_p(K)ⁿ ≅ Kⁿ are the canonical term isomorphisms, then the
degree-n transition component is e_pn⁻¹ ∘ e_qn. -/
theorem finiteCotruncationTransition_f (K : CochainComplex C ℕ) {p q : ℕ}
    (hpq : p ≤ q) (n : ℕ) (hn : n ≤ p) :
    (K.finiteCotruncationTransition hpq).f n =
      (K.finiteCotruncationXIso q n (hn.trans hpq)).hom ≫
        (K.finiteCotruncationXIso p n hn).inv := by
  let i : Fin (p + 1) := ⟨n, by omega⟩
  let eQ := K.finiteCotruncationXIso q n (hn.trans hpq)
  let eP := K.finiteCotruncationXIso p n hn
  have hf := (upEmbedding p).liftExtend_f
    (K.finiteCotruncationRestrictionIso hpq).hom
    ((upEmbedding p).hasLift_of_isTruncLE _) (i := i) rfl
  have hR : ((K.finiteCotruncation q).restrictionXIso (upEmbedding p) (i := i) rfl).inv =
      𝟙 ((K.finiteCotruncation q).X n) := rfl
  have hComponent : (K.finiteCotruncationRestrictionIso hpq).hom.f i = eQ.hom := rfl
  have hValue : (K.finiteCotruncationTransition hpq).f n =
      eQ.hom ≫ ((K.restriction (upEmbedding p)).extendXIso (upEmbedding p) (i := i) rfl).inv :=
    hf.trans ((congrArg₂ (fun z w => z ≫ w ≫
      ((K.restriction (upEmbedding p)).extendXIso (upEmbedding p) (i := i) rfl).inv)
        hR hComponent).trans (Category.id_comp _))
  have hCoordinate : eP.inv =
      ((K.restriction (upEmbedding p)).extendXIso (upEmbedding p) (i := i) rfl).inv := by
    unfold eP finiteCotruncationXIso HomologicalComplex.stupidTruncXIso
      HomologicalComplex.stupidTrunc
    rw [Iso.trans_inv]
    exact Category.id_comp _
  exact hValue.trans (congrArg (fun z => eQ.hom ≫ z) hCoordinate.symm)

theorem finiteCotruncationTransition_f_zero (K : CochainComplex C ℕ) {p q : ℕ}
    (hpq : p ≤ q) (n : ℕ) (hn : p < n) :
    (K.finiteCotruncationTransition hpq).f n = 0 :=
  (K.finiteCotruncation_isZero p n hn).eq_of_tgt _ _

/-- For a nonnegative cochain complex K in a category C with zero morphisms
and a zero object, and p≤q, the projections factor through the transition:
t_qp ∘ π_q = π_p as maps K → Cot_p(K). -/
@[reassoc]
theorem πFiniteCotruncation_transition (K : CochainComplex C ℕ)
    {p q : ℕ} (hpq : p ≤ q) :
    K.πFiniteCotruncation q ≫ K.finiteCotruncationTransition hpq =
      K.πFiniteCotruncation p := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n ≤ p
  · rw [HomologicalComplex.comp_f, πFiniteCotruncation_f K q n (hn.trans hpq),
      finiteCotruncationTransition_f K hpq n hn, πFiniteCotruncation_f K p n hn]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · exact (K.finiteCotruncation_isZero p n (by omega)).eq_of_tgt _ _

/-- Let C have zero morphisms and a zero object, K a nonnegative cochain
complex, and p≤q. If f:Cot_q(K) → Cot_p(K) satisfies f ∘ π_q=π_p,
then f equals the canonical transition t_qp. -/
theorem finiteCotruncationTransition_unique (K : CochainComplex C ℕ)
    {p q : ℕ} (hpq : p ≤ q)
    (f : K.finiteCotruncation q ⟶ K.finiteCotruncation p)
    (hf : K.πFiniteCotruncation q ≫ f = K.πFiniteCotruncation p) :
    f = K.finiteCotruncationTransition hpq := by
  apply (cancel_epi (K.πFiniteCotruncation q)).1
  exact hf.trans (K.πFiniteCotruncation_transition hpq).symm

@[simp]
theorem finiteCotruncationTransition_refl (K : CochainComplex C ℕ) (p : ℕ) :
    K.finiteCotruncationTransition (le_refl p) = 𝟙 _ := by
  apply (cancel_epi (K.πFiniteCotruncation p)).1
  rw [πFiniteCotruncation_transition, Category.comp_id]

/-- In a category C with zero morphisms and a zero object, for a nonnegative
cochain complex K and p≤q≤r, the transition maps satisfy
t_qp ∘ t_rq = t_rp. -/
@[reassoc]
theorem finiteCotruncationTransition_comp (K : CochainComplex C ℕ)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    K.finiteCotruncationTransition hqr ≫ K.finiteCotruncationTransition hpq =
      K.finiteCotruncationTransition (hpq.trans hqr) := by
  apply (cancel_epi (K.πFiniteCotruncation r)).1
  simp only [← Category.assoc, πFiniteCotruncation_transition]

/-- For a cochain map f:K → L in a category C with zero morphisms and a
zero object and p≤q, the transition maps commute with induced cotruncation
maps: t_qp(L) ∘ Cot_q(f) = Cot_p(f) ∘ t_qp(K). -/
@[reassoc]
theorem finiteCotruncationTransition_naturality {K L : CochainComplex C ℕ}
    (f : K ⟶ L) {p q : ℕ} (hpq : p ≤ q) :
    finiteCotruncationMap f q ≫ L.finiteCotruncationTransition hpq =
      K.finiteCotruncationTransition hpq ≫ finiteCotruncationMap f p := by
  apply (cancel_epi (K.πFiniteCotruncation q)).1
  rw [← Category.assoc, ← πFiniteCotruncation_naturality, Category.assoc,
    πFiniteCotruncation_transition, ← Category.assoc,
    πFiniteCotruncation_transition, ← πFiniteCotruncation_naturality]

/-- For a nonnegative cochain complex K in a category C with zero morphisms
and a zero object, the inverse system ℕᵒᵖ → CochainComplex(C,ℕ)
with value Cot_q(K) at q and transition t_qp for p≤q. -/
def finiteCotruncationSystem (K : CochainComplex C ℕ) :
    ℕᵒᵖ ⥤ CochainComplex C ℕ where
  obj q := K.finiteCotruncation q.unop
  map f := K.finiteCotruncationTransition (leOfHom f.unop)
  map_id q := finiteCotruncationTransition_refl K q.unop
  map_comp f g := (finiteCotruncationTransition_comp K
    (leOfHom g.unop) (leOfHom f.unop)).symm

/-- Let C have zero morphisms and a zero object and K be a nonnegative
cochain complex. The projections π_q:K → Cot_q(K) form a natural
transformation from the constant inverse system on K to its system of
finite cotruncations. -/
def πFiniteCotruncationSystem (K : CochainComplex C ℕ) :
    (Functor.const ℕᵒᵖ).obj K ⟶ finiteCotruncationSystem K where
  app q := K.πFiniteCotruncation q.unop
  naturality := by
    intro p q f
    change 𝟙 K ≫ K.πFiniteCotruncation q.unop =
      K.πFiniteCotruncation p.unop ≫ K.finiteCotruncationTransition (leOfHom f.unop)
    exact (Category.id_comp _).trans
      (K.πFiniteCotruncation_transition (leOfHom f.unop)).symm

/-- For a category C with zero morphisms and a zero object, a nonnegative
cochain complex K and a complex L on the initial interval [0,q], the
Hom-set equivalence
Hom(K|[0,q],L) ≃ Hom(K,extend₀(L)),
where extend₀ places zero objects outside the interval. This is the
restriction and extension-by-zero adjunction for the initial cochain
embedding. -/
def finiteRestrictionExtendHomEquiv (q : ℕ) (K : CochainComplex C ℕ)
    (L : HomologicalComplex C (upShape q)) :
    (K.restriction (upEmbedding q) ⟶ L) ≃ (K ⟶ L.extend (upEmbedding q)) :=
  (upEmbedding q).restrictionExtendHomEquiv K L

end Maps

section Homology

variable [Abelian C]

/-- For a nonnegative cochain complex K in an abelian category C and
n<q, the projection π_q:K → Cot_q(K) is a quasi-isomorphism in degree n:
its induced map Hⁿ(K) → Hⁿ(Cot_q(K)) is an isomorphism. -/
theorem πFiniteCotruncation_quasiIsoAt (K : CochainComplex C ℕ)
    (q n : ℕ) (hn : n < q) : QuasiIsoAt (K.πFiniteCotruncation q) n := by
  have hnq : n ≤ q := Nat.le_of_lt hn
  have hnext : (ComplexShape.up ℕ).next n ≤ q := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
    omega
  have hprev : (ComplexShape.up ℕ).prev n ≤ q := by
    cases n with
    | zero => simp only [CochainComplex.prev_nat_zero]; omega
    | succ n => simp only [CochainComplex.prev_nat_succ]; omega
  let f := K.πFiniteCotruncation q
  letI : IsIso (f.f ((ComplexShape.up ℕ).prev n)) := by
    change IsIso ((K.πFiniteCotruncation q).f ((ComplexShape.up ℕ).prev n))
    rw [πFiniteCotruncation_f K q _ hprev]
    infer_instance
  letI : IsIso (f.f n) := by
    change IsIso ((K.πFiniteCotruncation q).f n)
    rw [πFiniteCotruncation_f K q n hnq]
    infer_instance
  letI : IsIso (f.f ((ComplexShape.up ℕ).next n)) := by
    change IsIso ((K.πFiniteCotruncation q).f ((ComplexShape.up ℕ).next n))
    rw [πFiniteCotruncation_f K q _ hnext]
    infer_instance
  rw [quasiIsoAt_iff]
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) n).map f
  letI : Epi φ.τ₁ := inferInstanceAs (Epi (f.f ((ComplexShape.up ℕ).prev n)))
  letI : IsIso φ.τ₂ := inferInstanceAs (IsIso (f.f n))
  letI : Mono φ.τ₃ := inferInstanceAs (Mono (f.f ((ComplexShape.up ℕ).next n)))
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- For a nonnegative cochain complex K in an abelian category C and
n<q, the canonical isomorphism Hⁿ(K) ≅ Hⁿ(Cot_q(K)) whose forward map
is induced by the projection π_q. -/
def finiteCotruncationHomologyIso (K : CochainComplex C ℕ) (q n : ℕ) (hn : n < q) :
    K.homology n ≅ (K.finiteCotruncation q).homology n := by
  letI : QuasiIsoAt (K.πFiniteCotruncation q) n := K.πFiniteCotruncation_quasiIsoAt q n hn
  exact isoOfQuasiIsoAt (K.πFiniteCotruncation q) n

@[simp]
theorem finiteCotruncationHomologyIso_hom (K : CochainComplex C ℕ)
    (q n : ℕ) (hn : n < q) :
    (K.finiteCotruncationHomologyIso q n hn).hom =
      HomologicalComplex.homologyMap (K.πFiniteCotruncation q) n := rfl

/-- Let C be abelian, f:K → L a map of nonnegative cochain complexes and
n<q. If α_K:Hⁿ(K) ≅ Hⁿ(Cot_q(K)) and α_L are the isomorphisms induced
by the projections, their naturality square is
α_L ∘ Hⁿ(f) = Hⁿ(Cot_q(f)) ∘ α_K. -/
@[reassoc]
theorem finiteCotruncationHomologyIso_naturality {K L : CochainComplex C ℕ}
    (f : K ⟶ L) (q n : ℕ) (hn : n < q) :
    HomologicalComplex.homologyMap f n ≫ (L.finiteCotruncationHomologyIso q n hn).hom =
      (K.finiteCotruncationHomologyIso q n hn).hom ≫
        HomologicalComplex.homologyMap (finiteCotruncationMap f q) n := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (πFiniteCotruncation_naturality f q)
  simpa only [finiteCotruncationHomologyIso_hom, HomologicalComplex.homologyMap_comp] using h

end Homology

end CochainComplex
