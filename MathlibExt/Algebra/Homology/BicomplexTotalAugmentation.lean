/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TotalComplexSingle
public import MathlibExt.Algebra.Homology.TotalComplexMap
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

public meta import Lean.Elab.Tactic.Omega

/-!
# Total augmentations of bicomplexes

For a nonnegative chain bicomplex K in a preadditive category, the cokernel of the horizontal
row map K₁ → K₀ receives a canonical map from Tot(K), whenever these objects exist. It is the
cokernel projection on outer column zero and vanishes on positive columns; it commutes with the
total differential and is natural in K.

In a preadditive category with a zero object and finite coproducts, a chain or cochain bicomplex
map B → S(L), where S(L) places each term of L in inner degree zero, induces a total
augmentation Tot(B) → L. Its summand formulas, commuting-square naturality and construction from
natural transformations hold in both nonnegative directions.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u
universe u' v' w'

open CategoryTheory CategoryTheory.Limits



namespace HomologicalComplex₂

section FirstColumnCokernel

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
variable [HasCokernel (K.d 1 0)]

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. The first-column cokernel is
the chain complex coker(d_K,1,0), the quotient of the outer-degree-zero row K₀ by the incoming
row map from K₁. -/
abbrev firstColumnCokernel : ChainComplex C ℕ := cokernel (K.d 1 0)

variable [K.HasTotal (ComplexShape.down ℕ)]

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For n ∈ ℕ, the map p_n : Tot(K)_n → coker(d_K,1,0)_n restricts on
bidegree (0,n) to the degree-n cokernel projection and is zero on every summand with positive
outer degree. -/
def firstColumnCokernelProjectionX (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (firstColumnCokernel K).X n :=
  K.totalDesc fun p q h => by
    if hp : p = 0 then
      have hq : q = n := by
        change p + q = n at h
        simpa only [hp, Nat.zero_add] using h
      exact eqToHom (by subst p q; rfl) ≫ (cokernel.π (K.d 1 0)).f n
    else
      exact 0

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For n ∈ ℕ, the inclusion ι_{0,n} into Tot(K)_n satisfies ι_{0,n} ≫
p_n = (cokernel.π(d_K,1,0))_n. -/
@[reassoc]
theorem ι_firstColumnCokernelProjectionX_zero (n : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) ≫
      firstColumnCokernelProjectionX K n = (cokernel.π (K.d 1 0)).f n := by
  simp only [firstColumnCokernelProjectionX, HomologicalComplex₂.ι_totalDesc]
  simp

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For p,q,n ∈ ℕ with p+1+q=n, the summand inclusion from K_{p+1,q}
followed by p_n is zero. -/
@[reassoc]
theorem ι_firstColumnCokernelProjectionX_succ (p q n : ℕ) (h : p + 1 + q = n) :
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫
      firstColumnCokernelProjectionX K n = 0 := by
  simp only [firstColumnCokernelProjectionX, HomologicalComplex₂.ι_totalDesc,
    dite_eq_right (Nat.succ_ne_zero p)]

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For arbitrary p,q,n ∈ ℕ, the summand-or-zero map from K_{p+1,q} to
Tot(K)_n followed by p_n is zero, including degrees with p+1+q ≠ n. -/
@[reassoc]
theorem ιOrZero_firstColumnCokernelProjectionX_succ (p q n : ℕ) :
    K.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q n ≫
      firstColumnCokernelProjectionX K n = 0 := by
  by_cases h : p + 1 + q = n
  · rw [K.ιTotalOrZero_eq (ComplexShape.down ℕ) (p + 1) q n h,
      ι_firstColumnCokernelProjectionX_succ K p q n h]
  · rw [K.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) (p + 1) q n h,
      Limits.zero_comp]

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For p,q,n ∈ ℕ, the signed vertical contribution d₂ from K_{p+1,q}
into Tot(K)_n has zero composite with p_n : Tot(K)_n → coker(d_K,1,0)_n. -/
theorem d₂_firstColumnCokernelProjectionX_succ (p q n : ℕ) :
    K.d₂ (ComplexShape.down ℕ) (p + 1) q n ≫ firstColumnCokernelProjectionX K n = 0 := by
  cases q with
  | zero =>
    rw [K.d₂_eq_zero (ComplexShape.down ℕ) (p + 1) 0 n (by
      simp only [ChainComplex.next_nat_zero, ComplexShape.down_Rel, Nat.zero_add,
        Nat.one_ne_zero, not_false_eq_true]), Limits.zero_comp]
  | succ q =>
    rw [K.d₂_eq' (ComplexShape.down ℕ) (p + 1)
        (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) n,
      Linear.units_smul_comp, Category.assoc,
      ιOrZero_firstColumnCokernelProjectionX_succ K p q n,
      Limits.comp_zero, smul_zero]

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For p,q,n ∈ ℕ, the signed horizontal contribution d₁ from K_{p+2,q}
into Tot(K)_n has zero composite with p_n, because its target outer column is still positive. -/
theorem d₁_firstColumnCokernelProjectionX_succ_succ (p q n : ℕ) :
    K.d₁ (ComplexShape.down ℕ) (p + 2) q n ≫ firstColumnCokernelProjectionX K n = 0 := by
  rw [K.d₁_eq' (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (p + 2) (p + 1) from rfl) q n]
  change ((1 : ℤˣ) • ((K.d (p + 2) (p + 1)).f q ≫
      K.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q n)) ≫
    firstColumnCokernelProjectionX K n = 0
  rw [one_smul, Category.assoc,
    ιOrZero_firstColumnCokernelProjectionX_succ K p q n, Limits.comp_zero]

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For n ∈ ℕ, the degree maps satisfy p_{n+1} ≫ d_coker,n+1,n =
d_Tot(K),n+1,n ≫ p_n. Thus the full signed total differential is compatible with the cokernel
differential. -/
theorem firstColumnCokernelProjectionX_comm (n : ℕ) :
    firstColumnCokernelProjectionX K (n + 1) ≫ (firstColumnCokernel K).d (n + 1) n =
      (K.total (ComplexShape.down ℕ)).d (n + 1) n ≫
        firstColumnCokernelProjectionX K n := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change K.ιTotal (ComplexShape.down ℕ) p q (n + 1) h ≫
      (firstColumnCokernelProjectionX K (n + 1) ≫
        (firstColumnCokernel K).d (n + 1) n) =
    K.ιTotal (ComplexShape.down ℕ) p q (n + 1) h ≫
      ((K.D₁ (ComplexShape.down ℕ) (n + 1) n +
        K.D₂ (ComplexShape.down ℕ) (n + 1) n) ≫ firstColumnCokernelProjectionX K n)
  rw [← Category.assoc, ← Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
    K.ι_D₁ (ComplexShape.down ℕ) (n + 1) n p q h,
    K.ι_D₂ (ComplexShape.down ℕ) (n + 1) n p q h]
  cases p with
  | zero =>
    have hq : q = n + 1 := by
      change 0 + q = n + 1 at h
      simpa only [Nat.zero_add] using h
    subst q
    rw [ι_firstColumnCokernelProjectionX_zero K (n + 1),
      K.d₁_eq_zero (ComplexShape.down ℕ) 0 (n + 1) n (by
        simp only [ChainComplex.next_nat_zero, ComplexShape.down_Rel,
          Nat.zero_add, Nat.one_ne_zero, not_false_eq_true]),
      Limits.zero_comp, zero_add,
      K.d₂_eq (ComplexShape.down ℕ) 0
        (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) n (Nat.zero_add n)]
    change (cokernel.π (K.d 1 0)).f (n + 1) ≫ (firstColumnCokernel K).d (n + 1) n =
      ((1 : ℤˣ) • ((K.X 0).d (n + 1) n ≫
        K.ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n))) ≫
          firstColumnCokernelProjectionX K n
    rw [one_smul, Category.assoc, ι_firstColumnCokernelProjectionX_zero K n]
    exact (cokernel.π (K.d 1 0)).comm (n + 1) n
  | succ p =>
    rw [ι_firstColumnCokernelProjectionX_succ K p q (n + 1) h, Limits.zero_comp,
      d₂_firstColumnCokernelProjectionX_succ K p q n, add_zero]
    cases p with
    | zero =>
      have hq : q = n := by
        change 0 + 1 + q = n + 1 at h
        omega
      subst q
      rw [K.d₁_eq (ComplexShape.down ℕ)
        (show (ComplexShape.down ℕ).Rel 1 0 from rfl) n n (Nat.zero_add n)]
      change 0 = ((1 : ℤˣ) • ((K.d 1 0).f n ≫
        K.ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n))) ≫
          firstColumnCokernelProjectionX K n
      rw [one_smul, Category.assoc, ι_firstColumnCokernelProjectionX_zero K n]
      have hz := congrArg
        (fun f : K.X 1 ⟶ firstColumnCokernel K => f.f n) (cokernel.condition (K.d 1 0))
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using hz.symm
    | succ p =>
      exact (d₁_firstColumnCokernelProjectionX_succ_succ K p q n).symm

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. The maps p_n, equal to the cokernel projection on bidegree (0,n) and
zero on positive outer columns, form a chain map Tot(K) → coker(d_K,1,0). -/
def firstColumnCokernelProjection :
    K.total (ComplexShape.down ℕ) ⟶ firstColumnCokernel K :=
  ChainComplex.ofHom (firstColumnCokernelProjectionX K)
    (firstColumnCokernelProjectionX_comm K)

/-- Let C be preadditive, K a bicomplex of nonnegative chain complexes, and assume the cokernel of
its horizontal map d_K,1,0 : K₁ → K₀ exists in ChainComplex C ℕ. Assume also that K has a
nonnegative total complex. For n ∈ ℕ, the degree-n component of firstColumnCokernelProjection is
p_n : Tot(K)_n → coker(d_K,1,0)_n, the map specified by its first-column summand formulas. -/
@[simp]
theorem firstColumnCokernelProjection_f (n : ℕ) :
    (firstColumnCokernelProjection K).f n = firstColumnCokernelProjectionX K n := rfl

variable {K L} [HasCokernel (L.d 1 0)]

/-- Let C be preadditive and f : K → L a map of nonnegative chain bicomplexes. Suppose the cokernels
of d_K,1,0 and d_L,1,0 exist as chain complexes. The commuting square with row maps f₁ and f₀
induces firstColumnCokernelMap f : coker(d_K,1,0) → coker(d_L,1,0). -/
def firstColumnCokernelMap (f : K ⟶ L) :
    firstColumnCokernel K ⟶ firstColumnCokernel L :=
  cokernel.map (K.d 1 0) (L.d 1 0) (f.f 1) (f.f 0) (f.comm 1 0).symm

omit [K.HasTotal (ComplexShape.down ℕ)] in
/-- Let C be preadditive and f : K → L a map of nonnegative chain bicomplexes with the two
first-column cokernels. The induced map c satisfies cokernel.π(d_K,1,0) ≫ c = f₀ ≫
cokernel.π(d_L,1,0) as chain maps from K₀. -/
@[reassoc]
theorem firstColumnCokernelMap_π (f : K ⟶ L) :
    cokernel.π (K.d 1 0) ≫ firstColumnCokernelMap f =
      f.f 0 ≫ cokernel.π (L.d 1 0) := by
  simp only [firstColumnCokernelMap, cokernel.map, cokernel.π_desc]

variable [L.HasTotal (ComplexShape.down ℕ)]

/-- Let C be preadditive and f : K → L a map of nonnegative chain bicomplexes. Assume both
first-column cokernels and both total complexes exist. Their canonical projections satisfy
Tot(f) ≫ p_L = p_K ≫ firstColumnCokernelMap(f). -/
theorem firstColumnCokernelProjection_naturality (f : K ⟶ L) :
    HomologicalComplex₂.total.map f (ComplexShape.down ℕ) ≫ firstColumnCokernelProjection L =
      firstColumnCokernelProjection K ≫ firstColumnCokernelMap f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, firstColumnCokernelProjection_f]
  rw [← Category.assoc,
    HomologicalComplex₂.ιTotal_map K L f (ComplexShape.down ℕ) p q n h]
  cases p with
  | zero =>
    have hq : q = n := by
      change 0 + q = n at h
      simpa only [Nat.zero_add] using h
    subst q
    rw [Category.assoc, ι_firstColumnCokernelProjectionX_zero L n,
      ← Category.assoc, ι_firstColumnCokernelProjectionX_zero K n]
    have hz := congrArg
      (fun φ : K.X 0 ⟶ firstColumnCokernel L => φ.f n) (firstColumnCokernelMap_π f)
    simpa only [HomologicalComplex.comp_f] using hz.symm
  | succ p =>
    rw [Category.assoc, ι_firstColumnCokernelProjectionX_succ L p q n h,
      Limits.comp_zero, ← Category.assoc,
      ι_firstColumnCokernelProjectionX_succ K p q n h, Limits.zero_comp]

end FirstColumnCokernel



variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

section DownNat

variable {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)}
variable {L L' : ChainComplex C ℕ}

/-- Let C be preadditive with a zero object and finite coproducts. Let B be a bicomplex with both
nonnegative chain directions, L a nonnegative chain complex, and f : B → S(L) a bicomplex map,
where S(L) puts each L_p in inner degree zero. The total augmentation is Tot(B) → Tot(S(L)) ≅ L,
obtained by totalizing f and composing with the canonical single-complex total isomorphism. -/
noncomputable def totalAugmentationDownNat
    (f : B ⟶ singleMapBicomplexFunctorDownNat.obj L) :
    B.total (ComplexShape.down ℕ) ⟶ L :=
  HomologicalComplex₂.total.map f (ComplexShape.down ℕ) ≫
    (single₀MapTotalIso L).hom

/-- Let C be preadditive with a zero object and finite coproducts. Let B be a bicomplex with both
nonnegative chain directions, L a nonnegative chain complex, and f : B → S(L) a bicomplex map,
where S(L) puts each L_p in inner degree zero. For p,q,n ∈ ℕ with p+q=n, the inclusion ι_B,p,q
followed by the degree-n augmentation equals f_{p,q} ≫ ι_S(L),p,q ≫ e_L.hom_n, where e_L :
Tot(S(L)) ≅ L. This sends inner-positive summands to zero. -/
@[reassoc]
theorem ιTotal_comp_totalAugmentationDownNat
    (f : B ⟶ singleMapBicomplexFunctorDownNat.obj L)
    (p q n : ℕ) (h : p + q = n) :
    B.ιTotal (ComplexShape.down ℕ) p q n h ≫
        (totalAugmentationDownNat f).f n =
      (f.f p).f q ≫
        (singleMapBicomplexFunctorDownNat.obj L).ιTotal
          (ComplexShape.down ℕ) p q n h ≫
            (single₀MapTotalIso L).hom.f n := by
  simp only [totalAugmentationDownNat, HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc]

/-- Let C be preadditive with a zero object and finite coproducts. Let B be a bicomplex with both
nonnegative chain directions, L a nonnegative chain complex, and f : B → S(L) a bicomplex map,
where S(L) puts each L_p in inner degree zero. For p ∈ ℕ, the inclusion ι_B,p,0 followed by the
degree-p total augmentation equals f_{p,0} followed by the canonical identification S(L)_{p,0} ≅
L_p. -/
@[reassoc]
theorem ιTotal_comp_totalAugmentationDownNat_zero
    (f : B ⟶ singleMapBicomplexFunctorDownNat.obj L) (p : ℕ) :
    B.ιTotal (ComplexShape.down ℕ) p 0 p (Nat.add_zero p) ≫
        (totalAugmentationDownNat f).f p =
      (f.f p).f 0 ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 0 (L.X p)).hom := by
  rw [ιTotal_comp_totalAugmentationDownNat,
    ιTotal_comp_singleMapTotalIsoDownNat_hom_single]

/-- Let C be preadditive with a zero object and finite coproducts. Let e : B → B′ be a map of
nonnegative chain bicomplexes, g : L → L′ a chain map, and f : B → S(L), f′ : B′ → S(L′) maps to
their componentwise degree-zero bicomplexes. If e ≫ f′ = f ≫ S(g), then Tot(e) ≫ aug(f′) =
aug(f) ≫ g. -/
theorem totalAugmentationDownNat_naturality
    (e : B ⟶ B') (g : L ⟶ L')
    (f : B ⟶ singleMapBicomplexFunctorDownNat.obj L)
    (f' : B' ⟶ singleMapBicomplexFunctorDownNat.obj L')
    (h : e ≫ f' = f ≫ singleMapBicomplexFunctorDownNat.map g) :
    HomologicalComplex₂.total.map e (ComplexShape.down ℕ) ≫
        totalAugmentationDownNat f' =
      totalAugmentationDownNat f ≫ g := by
  calc
    HomologicalComplex₂.total.map e (ComplexShape.down ℕ) ≫
          totalAugmentationDownNat f' =
        HomologicalComplex₂.total.map (e ≫ f')
            (ComplexShape.down ℕ) ≫
          (single₀MapTotalIso L').hom := by
            rw [totalAugmentationDownNat, ← Category.assoc,
              ← HomologicalComplex₂.total.map_comp]
    _ = HomologicalComplex₂.total.map
          (f ≫ singleMapBicomplexFunctorDownNat.map g)
            (ComplexShape.down ℕ) ≫
          (single₀MapTotalIso L').hom := by rw [h]
    _ = HomologicalComplex₂.total.map f (ComplexShape.down ℕ) ≫
          HomologicalComplex₂.total.map
              (singleMapBicomplexFunctorDownNat.map g)
              (ComplexShape.down ℕ) ≫
            (single₀MapTotalIso L').hom := by
              rw [HomologicalComplex₂.total.map_comp, Category.assoc]
    _ = HomologicalComplex₂.total.map f (ComplexShape.down ℕ) ≫
          (single₀MapTotalIso L).hom ≫ g := by
            rw [singleMapTotalIsoDownNat_hom_naturality]
    _ = totalAugmentationDownNat f ≫ g := by
          rw [totalAugmentationDownNat, Category.assoc]

variable {D : Type w} [Category D]

/-- Let C be preadditive with a zero object and finite coproducts. Let D be a category, F a functor
from D to nonnegative chain bicomplexes, G a functor from D to nonnegative chain complexes, and
α : F → S ∘ G a natural transformation. The componentwise total augmentations define a natural
transformation Tot ∘ F → G, with component at X equal to aug(α_X). -/
noncomputable def totalAugmentationNatTransDownNat
    (F : D ⥤ HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (G : D ⥤ ChainComplex C ℕ)
    (α : F ⟶ G ⋙ singleMapBicomplexFunctorDownNat) :
    F ⋙ HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⟶ G where
  app X := totalAugmentationDownNat (α.app X)
  naturality {X Y} f :=
    totalAugmentationDownNat_naturality (F.map f) (G.map f)
      (α.app X) (α.app Y) (α.naturality f)

@[simp]
theorem totalAugmentationNatTransDownNat_app
    (F : D ⥤ HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (G : D ⥤ ChainComplex C ℕ)
    (α : F ⟶ G ⋙ singleMapBicomplexFunctorDownNat) (X : D) :
    (totalAugmentationNatTransDownNat F G α).app X =
      totalAugmentationDownNat (α.app X) :=
  rfl

end DownNat

section UpNat

variable {B B' : HomologicalComplex₂ C (ComplexShape.up ℕ)
    (ComplexShape.up ℕ)}
variable {L L' : CochainComplex C ℕ}

/-- Let C be preadditive with a zero object and finite coproducts. Let B be a bicomplex with both
nonnegative cochain directions, L a nonnegative cochain complex, and f : B → S(L) a bicomplex
map, where S(L) puts each L_p in inner degree zero. The total augmentation is Tot(B) → Tot(S(L))
≅ L, obtained by totalizing f and composing with the canonical single-complex total isomorphism. -/
noncomputable def totalAugmentationUpNat
    (f : B ⟶ singleMapBicomplexFunctorUpNat.obj L) :
    B.total (ComplexShape.up ℕ) ⟶ L :=
  HomologicalComplex₂.total.map f (ComplexShape.up ℕ) ≫
    (singleMapTotalIsoUpNat L).hom

/-- Let C be preadditive with a zero object and finite coproducts. Let B be a bicomplex with both
nonnegative cochain directions, L a nonnegative cochain complex, and f : B → S(L) a bicomplex
map, where S(L) puts each L_p in inner degree zero. For p,q,n ∈ ℕ with p+q=n, the inclusion
ι_B,p,q followed by the degree-n augmentation equals f_{p,q} ≫ ι_S(L),p,q ≫ e_L.hom_n, where e_L
: Tot(S(L)) ≅ L. This sends inner-positive summands to zero. -/
@[reassoc]
theorem ιTotal_comp_totalAugmentationUpNat
    (f : B ⟶ singleMapBicomplexFunctorUpNat.obj L)
    (p q n : ℕ) (h : p + q = n) :
    B.ιTotal (ComplexShape.up ℕ) p q n h ≫
        (totalAugmentationUpNat f).f n =
      (f.f p).f q ≫
        (singleMapBicomplexFunctorUpNat.obj L).ιTotal
          (ComplexShape.up ℕ) p q n h ≫
            (singleMapTotalIsoUpNat L).hom.f n := by
  simp only [totalAugmentationUpNat, HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc]

/-- Let C be preadditive with a zero object and finite coproducts. Let B be a bicomplex with both
nonnegative cochain directions, L a nonnegative cochain complex, and f : B → S(L) a bicomplex
map, where S(L) puts each L_p in inner degree zero. For p ∈ ℕ, the inclusion ι_B,p,0 followed by
the degree-p total augmentation equals f_{p,0} followed by the canonical identification
S(L)_{p,0} ≅ L_p. -/
@[reassoc]
theorem ιTotal_comp_totalAugmentationUpNat_zero
    (f : B ⟶ singleMapBicomplexFunctorUpNat.obj L) (p : ℕ) :
    B.ιTotal (ComplexShape.up ℕ) p 0 p (Nat.add_zero p) ≫
        (totalAugmentationUpNat f).f p =
      (f.f p).f 0 ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℕ) 0 (L.X p)).hom := by
  rw [ιTotal_comp_totalAugmentationUpNat,
    ιTotal_comp_singleMapTotalIsoUpNat_hom_single]

/-- Let C be preadditive with a zero object and finite coproducts. Let e : B → B′ be a map of
nonnegative cochain bicomplexes, g : L → L′ a cochain map, and f : B → S(L), f′ : B′ → S(L′)
maps to their componentwise degree-zero bicomplexes. If e ≫ f′ = f ≫ S(g), then Tot(e) ≫ aug(f′)
= aug(f) ≫ g. -/
theorem totalAugmentationUpNat_naturality
    (e : B ⟶ B') (g : L ⟶ L')
    (f : B ⟶ singleMapBicomplexFunctorUpNat.obj L)
    (f' : B' ⟶ singleMapBicomplexFunctorUpNat.obj L')
    (h : e ≫ f' = f ≫ singleMapBicomplexFunctorUpNat.map g) :
    HomologicalComplex₂.total.map e (ComplexShape.up ℕ) ≫
        totalAugmentationUpNat f' =
      totalAugmentationUpNat f ≫ g := by
  calc
    HomologicalComplex₂.total.map e (ComplexShape.up ℕ) ≫
          totalAugmentationUpNat f' =
        HomologicalComplex₂.total.map (e ≫ f')
            (ComplexShape.up ℕ) ≫
          (singleMapTotalIsoUpNat L').hom := by
            rw [totalAugmentationUpNat, ← Category.assoc,
              ← HomologicalComplex₂.total.map_comp]
    _ = HomologicalComplex₂.total.map
          (f ≫ singleMapBicomplexFunctorUpNat.map g)
            (ComplexShape.up ℕ) ≫
          (singleMapTotalIsoUpNat L').hom := by rw [h]
    _ = HomologicalComplex₂.total.map f (ComplexShape.up ℕ) ≫
          HomologicalComplex₂.total.map
              (singleMapBicomplexFunctorUpNat.map g)
              (ComplexShape.up ℕ) ≫
            (singleMapTotalIsoUpNat L').hom := by
              rw [HomologicalComplex₂.total.map_comp, Category.assoc]
    _ = HomologicalComplex₂.total.map f (ComplexShape.up ℕ) ≫
          (singleMapTotalIsoUpNat L).hom ≫ g := by
            rw [singleMapTotalIsoUpNat_hom_naturality]
    _ = totalAugmentationUpNat f ≫ g := by
          rw [totalAugmentationUpNat, Category.assoc]

variable {D : Type w} [Category D]

/-- Let C be preadditive with a zero object and finite coproducts. Let D be a category, F a functor
from D to nonnegative cochain bicomplexes, G a functor from D to nonnegative cochain complexes,
and α : F → S ∘ G a natural transformation. The componentwise total augmentations define a
natural transformation Tot ∘ F → G, with component at X equal to aug(α_X). -/
noncomputable def totalAugmentationNatTransUpNat
    (F : D ⥤ HomologicalComplex₂ C (ComplexShape.up ℕ)
      (ComplexShape.up ℕ))
    (G : D ⥤ CochainComplex C ℕ)
    (α : F ⟶ G ⋙ singleMapBicomplexFunctorUpNat) :
    F ⋙ HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) (ComplexShape.up ℕ) ⟶ G where
  app X := totalAugmentationUpNat (α.app X)
  naturality {X Y} f :=
    totalAugmentationUpNat_naturality (F.map f) (G.map f)
      (α.app X) (α.app Y) (α.naturality f)

@[simp]
theorem totalAugmentationNatTransUpNat_app
    (F : D ⥤ HomologicalComplex₂ C (ComplexShape.up ℕ)
      (ComplexShape.up ℕ))
    (G : D ⥤ CochainComplex C ℕ)
    (α : F ⟶ G ⋙ singleMapBicomplexFunctorUpNat) (X : D) :
    (totalAugmentationNatTransUpNat F G α).app X =
      totalAugmentationUpNat (α.app X) :=
  rfl

end UpNat

end HomologicalComplex₂

end
