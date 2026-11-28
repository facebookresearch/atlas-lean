/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationNaturality
public import MathlibExt.Algebra.Homology.TotalHomotopy
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison
public import MathlibExt.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Vertical homotopies of complete horizontal filtrations

Let C be preadditive with a zero object and finite coproducts, and f,g:K→L maps of
first-quadrant bicomplexes. A homotopy h:flip f≃flip g gives a homotopy H:Tot f≃Tot g whose
component K_{p,q}→L_{p,q+1} is (-1)^p times the vertical component of h. Since horizontal degree
p is unchanged, H restricts to every finite horizontal cutoff and every complete cut i∈ℤ∪{⊥,⊤}.
These restrictions commute termwise with inclusions into the total complex and transitions
between filtration stages.

Extend chain degree r to cochain degree -r. The stage homotopies then lower cochain degree by
one and remain strictly compatible with all filtration arrows. For an interval i→j, they induce
a homotopy on the relative cone. Under Cone(F_i→F_j)^n≅F_i^{n+1}⊕F_j^n, its component to degree
m is diag(-h_i^{n+1,m+1},h_j^{n,m}). The lower coordinate therefore has a negative shift sign,
while the upper coordinate is unshifted. The generic cone-map construction assumes exactly the
two commuting map squares and the componentwise homotopy square. Category universes are
arbitrary.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  {f g : K ⟶ L}
  (h : _root_.Homotopy (flipMap f) (flipMap g))

local notation "c" => ComplexShape.down ℕ

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. This is the chain homotopy H:Tot
f≃Tot g. In total degree n=p+q, its component on K_{p,q} is (-1)^p times
h_{q,q+1,p}:K_{p,q}→L_{p,q+1}, followed by inclusion into total degree n+1. It satisfies (Tot
f)_n−(Tot g)_n=d^K_{n,n-1}≫H_{n-1,n}+H_{n,n+1}≫d^L_{n+1,n}. -/
def verticalTotalHomotopy :
    _root_.Homotopy (total.map f c) (total.map g c) :=
  totalMapHomotopy₂ c h

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, K,L bicomplexes of shape (down ℕ,down ℕ), f,g:K→L
and h a homotopy from flip f to flip g. For p,q,n∈ℕ with p+q=n, let ι^K_{p,q}:K_{p,q}→(Tot K)_n
and ι^L_{p,q+1}:L_{p,q+1}→(Tot L)_{n+1} be total-summand inclusions. The signed total homotopy H
obeys ι^K_{p,q}≫H_{n,n+1}=(-1)^p•(h_{q,q+1,p}≫ι^L_{p,q+1}). Thus it preserves horizontal degree
p while raising the vertical and total degrees by one. -/
@[reassoc]
theorem ιTotal_verticalTotalHomotopy_hom (p q n : ℕ) (hn : p + q = n) :
    K.ιTotal c p q n hn ≫ (verticalTotalHomotopy h).hom n (n + 1) =
      (-1 : ℤˣ) ^ p • ((h.hom q (q + 1)).f p ≫
        L.ιTotal c p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  simp only [verticalTotalHomotopy, totalMapHomotopy₂, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Homotopy.compLeft_hom, Homotopy.compRight_hom,
    Pi.zero_apply, zero_add, add_zero, totalMapHomotopy₁]
  rw [← Category.assoc, ιTotal_totalFlipIso_f_inv]
  simp only [Linear.units_smul_comp]
  rw [ιTotal_totalHomotopy₁Hom_assoc (K := K.flip) (L := L.flip) h c
    (q + 1) q p n (n + 1) (by change q + p = n; omega)
      (ComplexShape.prev_eq' c (show ComplexShape.Rel c (q + 1) q from rfl))]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTotalOrZero_eq L.flip c (q + 1) p (n + 1)
      (by change (q + 1) + p = n + 1; omega),
    ιTotal_totalFlipIso_f_hom]
  simp only [Linear.comp_units_smul, smul_smul]
  congr 1
  have he : ComplexShape.ε₁ c c c (q + 1, p) = 1 := rfl
  rw [HomologicalComplex.ComplexShape.σ_down_ℕ, HomologicalComplex.ComplexShape.σ_down_ℕ,
    he, one_mul, Nat.mul_add, Nat.mul_one, pow_add, ← mul_assoc, Int.units_mul_self, one_mul]

/-- For k,n∈ℕ and a pair (p,q) with p+q=n and p≤k, this map sends the index to (p,q+1). The new pair
satisfies p+(q+1)=n+1 and retains p≤k, so it lies in the same horizontal filtration stage in the
next total degree. -/
def horizontalFilteredTotalHomotopyIndex {k n : ℕ}
    (pq : DownNatHorizontalFilteredFiber n k) : DownNatHorizontalFilteredFiber (n + 1) k :=
  ⟨⟨(pq.val.val.1, pq.val.val.2 + 1), by
    have hs := pq.val.property
    change pq.val.val.1 + pq.val.val.2 = n at hs
    change pq.val.val.1 + (pq.val.val.2 + 1) = n + 1
    omega⟩, pq.property⟩

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For k,n,m∈ℕ, write G^fin_k for the
finite horizontal stage, ι^K_{k,n} for its inclusion into (Tot K)_n and r^L_{k,m} for the
projection onto the retained horizontal summands. This morphism (G^fin_k(K))_n→(G^fin_k(L))_m is
H^k_{n,m}=ι^K_{k,n}≫H_{n,m}≫r^L_{k,m}, where H is the signed vertical total homotopy. -/
def horizontalFilteredTotalHomotopyHom (k n m : ℕ) :
    horizontalFilteredTotalObj K k n ⟶ horizontalFilteredTotalObj L k m :=
  horizontalFilteredTotalToTotal K k n ≫ (verticalTotalHomotopy h).hom n m ≫
    totalToHorizontalFilteredTotal L k m

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, K,L bicomplexes of shape (down ℕ,down ℕ), f,g:K→L
and h a homotopy from flip f to flip g. For k,n∈ℕ and (p,q) with p+q=n and p≤k, let ι^K_{k,p,q}
and ι^L_{k,p,q+1} be finite-stage summand inclusions. The restricted component H^k_{n,n+1}
satisfies ι^K_{k,p,q}≫H^k_{n,n+1}=(-1)^p•(h_{q,q+1,p}≫ι^L_{k,p,q+1}). The target summand remains
in stage k, including when p=k. -/
@[reassoc]
theorem horizontalFilteredTotalHomotopyHom_ι (k n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    horizontalFilteredTotalι K k n pq ≫ horizontalFilteredTotalHomotopyHom h k n (n + 1) =
      (-1 : ℤˣ) ^ pq.val.val.1 •
        ((h.hom pq.val.val.2 (pq.val.val.2 + 1)).f pq.val.val.1 ≫
          horizontalFilteredTotalι L k (n + 1) (horizontalFilteredTotalHomotopyIndex pq)) := by
  unfold horizontalFilteredTotalHomotopyHom
  rw [← Category.assoc, horizontalFilteredTotalι_toTotal]
  rw [ιTotal_verticalTotalHomotopy_hom_assoc h _ _ _ pq.val.property]
  rw [Linear.units_smul_comp, Category.assoc, ιTotal_totalToHorizontalFilteredTotal,
    dite_eq_left pq.property]
  rfl

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, K,L bicomplexes of shape (down ℕ,down ℕ), f,g:K→L
and h a homotopy from flip f to flip g. For k,n,m∈ℕ with m≠n+1, the restricted signed homotopy
component H^k_{n,m}:(G^fin_k(K))_n→(G^fin_k(L))_m is zero. This is the vanishing condition for a
homotopy of chain complexes of shape down ℕ. -/
theorem horizontalFilteredTotalHomotopyHom_zero (k n m : ℕ)
    (hrel : ¬ComplexShape.Rel c m n) : horizontalFilteredTotalHomotopyHom h k n m = 0 := by
  unfold horizontalFilteredTotalHomotopyHom
  rw [(verticalTotalHomotopy h).zero n m hrel]
  simp

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, K,L bicomplexes of shape (down ℕ,down ℕ), f,g:K→L
and h a homotopy from flip f to flip g. For k,n,m∈ℕ, let H^k be the restricted finite-stage
components, H the signed total homotopy, and ι^K_k,ι^L_k the finite-stage inclusions into Tot K
and Tot L. Then H^k_{n,m}≫(ι^L_k)_m=(ι^K_k)_n≫H_{n,m}. This equality holds for every pair of
degrees, with zero components when m≠n+1. -/
@[reassoc]
theorem horizontalFilteredTotalHomotopyHom_toTotal (k n m : ℕ) :
    horizontalFilteredTotalHomotopyHom h k n m ≫ horizontalFilteredTotalToTotal L k m =
      horizontalFilteredTotalToTotal K k n ≫ (verticalTotalHomotopy h).hom n m := by
  by_cases hnm : n + 1 = m
  · subst m
    dsimp only [horizontalFilteredTotalObj]
    apply Sigma.hom_ext
    intro pq
    have hComponent :
        horizontalFilteredTotalι K k n pq ≫
            (horizontalFilteredTotalHomotopyHom h k n (n + 1) ≫
              horizontalFilteredTotalToTotal L k (n + 1)) =
          horizontalFilteredTotalι K k n pq ≫
            (horizontalFilteredTotalToTotal K k n ≫
              (verticalTotalHomotopy h).hom n (n + 1)) := by
      rw [horizontalFilteredTotalHomotopyHom_ι_assoc]
      rw [Linear.units_smul_comp, Category.assoc, horizontalFilteredTotalι_toTotal]
      rw [← Category.assoc, horizontalFilteredTotalι_toTotal,
        ιTotal_verticalTotalHomotopy_hom]
      rfl
    simpa only [horizontalFilteredTotalι, id_eq] using hComponent
  · rw [horizontalFilteredTotalHomotopyHom_zero h k n m hnm,
      (verticalTotalHomotopy h).zero n m hnm]
    simp

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For k∈ℕ, this is a chain homotopy
H^k:G^fin_k(f)≃G^fin_k(g) between the induced maps on the finite horizontal stages. Its
components are the restrictions of the signed total homotopy, it is zero unless the target
degree is the source degree plus one, and its homotopy equation is
G^fin_k(f)−G^fin_k(g)=dH^k+H^kd. -/
def horizontalFilteredTotalHomotopy (k : ℕ) :
    _root_.Homotopy (horizontalFilteredTotalComplexMapOfBicomplex f k)
      (horizontalFilteredTotalComplexMapOfBicomplex g k) where
  hom := horizontalFilteredTotalHomotopyHom h k
  zero n m hrel := horizontalFilteredTotalHomotopyHom_zero h k n m hrel
  comm n := by
    let iK := horizontalFilteredTotalComplexToTotal K k
    let iL := horizontalFilteredTotalComplexToTotal L k
    have hfac :
        (fun n m => horizontalFilteredTotalHomotopyHom h k n m ≫ iL.f m) =
          (fun n m => iK.f n ≫ (verticalTotalHomotopy h).hom n m) := by
      funext n m
      simpa only [iK, iL, horizontalFilteredTotalComplexToTotal] using
        horizontalFilteredTotalHomotopyHom_toTotal h k n m
    have hd : dNext n (horizontalFilteredTotalHomotopyHom h k) ≫ iL.f n =
        iK.f n ≫ dNext n (verticalTotalHomotopy h).hom := by
      rw [← dNext_comp_right, hfac, dNext_comp_left]
    have hp : prevD n (horizontalFilteredTotalHomotopyHom h k) ≫ iL.f n =
        iK.f n ≫ prevD n (verticalTotalHomotopy h).hom := by
      rw [← prevD_comp_right, hfac, prevD_comp_left]
    have hf : (horizontalFilteredTotalComplexMapOfBicomplex f k).f n ≫ iL.f n =
        iK.f n ≫ (total.map f c).f n := by
      simpa only [iK, iL, horizontalFilteredTotalComplexToTotal,
        horizontalFilteredTotalComplexMapOfBicomplex] using
        horizontalFilteredTotalMapOfBicomplex_toTotal f k n
    have hg : (horizontalFilteredTotalComplexMapOfBicomplex g k).f n ≫ iL.f n =
        iK.f n ≫ (total.map g c).f n := by
      simpa only [iK, iL, horizontalFilteredTotalComplexToTotal,
        horizontalFilteredTotalComplexMapOfBicomplex] using
        horizontalFilteredTotalMapOfBicomplex_toTotal g k n
    apply (cancel_mono (horizontalFilteredTotalToTotal L k n)).mp
    have hComm :
        (horizontalFilteredTotalComplexMapOfBicomplex f k).f n ≫ iL.f n =
          (dNext n (horizontalFilteredTotalHomotopyHom h k) +
            prevD n (horizontalFilteredTotalHomotopyHom h k) +
            (horizontalFilteredTotalComplexMapOfBicomplex g k).f n) ≫ iL.f n := by
      rw [hf, (verticalTotalHomotopy h).comm n]
      simp only [Preadditive.comp_add, Preadditive.add_comp]
      rw [hd, hp, hg]
    simpa only [iL, horizontalFilteredTotalComplexToTotal] using hComm

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, K,L bicomplexes of shape (down ℕ,down ℕ), f,g:K→L
and h a homotopy from flip f to flip g. For k,n,m∈ℕ, let H^k:G^fin_k(f)≃G^fin_k(g), H:Tot f≃Tot
g and ι^K_k,ι^L_k be the finite-stage inclusions. Then (H^k)_{n,m}≫(ι^L_k)_m=(ι^K_k)_n≫H_{n,m}.
The equality compares the homotopy components after inclusion in the same total complexes. -/
@[reassoc]
theorem horizontalFilteredTotalHomotopy_toTotal (k n m : ℕ) :
    (horizontalFilteredTotalHomotopy h k).hom n m ≫
        (horizontalFilteredTotalComplexToTotal L k).f m =
      (horizontalFilteredTotalComplexToTotal K k).f n ≫ (verticalTotalHomotopy h).hom n m :=
  horizontalFilteredTotalHomotopyHom_toTotal h k n m

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, K,L bicomplexes of shape (down ℕ,down ℕ), f,g:K→L
and h a homotopy from flip f to flip g. For k≤l and n,m∈ℕ, write t^K_{k,l}:G^fin_k(K)→G^fin_l(K)
and t^L_{k,l} for the stage transitions, and H^k,H^l for the restricted homotopies. Their
components satisfy (t^K_{k,l})_n≫(H^l)_{n,m}=(H^k)_{n,m}≫(t^L_{k,l})_m. -/
theorem horizontalFilteredTotalHomotopy_naturality {k l : ℕ} (hkl : k ≤ l) (n m : ℕ) :
    (horizontalFilteredTotalComplexMap K hkl).f n ≫
        (horizontalFilteredTotalHomotopy h l).hom n m =
      (horizontalFilteredTotalHomotopy h k).hom n m ≫
        (horizontalFilteredTotalComplexMap L hkl).f m := by
  have hNat :
      horizontalFilteredTotalMap K hkl n ≫ horizontalFilteredTotalHomotopyHom h l n m =
        horizontalFilteredTotalHomotopyHom h k n m ≫ horizontalFilteredTotalMap L hkl m := by
    apply (cancel_mono (horizontalFilteredTotalToTotal L l m)).mp
    rw [Category.assoc, horizontalFilteredTotalHomotopyHom_toTotal,
      ← Category.assoc, horizontalFilteredTotalMap_toTotal,
      Category.assoc, horizontalFilteredTotalMap_toTotal,
      horizontalFilteredTotalHomotopyHom_toTotal]
  simpa only [horizontalFilteredTotalComplexMap, horizontalFilteredTotalHomotopy] using hNat

/-- Let C be preadditive with a zero object and finite coproducts, φ:K→L a morphism of
first-quadrant bicomplexes and a∈ℤ with a≥0. If e_K:G_a(K)≅G^fin_a(K) and e_L are the
complete-to-finite comparisons, then e_K.hom≫G^fin_a(φ)≫e_L.inv=G_a(φ). Thus the complete-stage
map is the finite-stage map transported at both endpoints. -/
theorem horizontalCompleteFilteredTotalComplexFiniteIso_conjugate_map
    (φ : K ⟶ L) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexMapOfBicomplex φ a.toNat ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex φ (a : EInt) := by
  rw [← Category.assoc, horizontalCompleteFilteredTotalComplexFiniteIso_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For a∈ℤ with a≥0, let
e_K:G_a(K)≅G^fin_a(K) and e_L be the complete-to-finite stage isomorphisms. This is the homotopy
G_a(f)≃G_a(g) obtained from H^a:G^fin_a(f)≃G^fin_a(g) by precomposition with e_K.hom and
postcomposition with e_L.inv. The stage-map conjugation identities identify its endpoints with
the complete-stage maps. -/
def horizontalCompleteFilteredTotalHomotopyOfNonneg (a : ℤ) (ha : 0 ≤ a) :
    _root_.Homotopy (horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt))
      (horizontalCompleteFilteredTotalComplexMapOfBicomplex g (a : EInt)) := by
  let H := ((horizontalFilteredTotalHomotopy h a.toNat).compRight
    (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv).compLeft
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom
  have hf : (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
      (horizontalFilteredTotalComplexMapOfBicomplex f a.toNat ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) := by
    exact horizontalCompleteFilteredTotalComplexFiniteIso_conjugate_map f a ha
  have hg : (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
      (horizontalFilteredTotalComplexMapOfBicomplex g a.toNat ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex g (a : EInt) := by
    exact horizontalCompleteFilteredTotalComplexFiniteIso_conjugate_map g a ha
  exact (Homotopy.ofEq hf.symm).trans (H.trans (Homotopy.ofEq hg))

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For a∈ℤ with a≥0 and n,m∈ℕ, let
e_K:G_a(K)≅G^fin_a(K), e_L and H^a:G^fin_a(f)≃G^fin_a(g). The transported complete-stage
homotopy has component (e_K.hom)_n≫(H^a)_{n,m}≫(e_L.inv)_m. This formula specifies its component
in the complete-stage source and target terms. -/
theorem horizontalCompleteFilteredTotalHomotopyOfNonneg_hom (a : ℤ) (ha : 0 ≤ a)
    (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha).hom n m =
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalHomotopy h a.toNat).hom n m ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv.f m) := by
  simp only [horizontalCompleteFilteredTotalHomotopyOfNonneg, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Homotopy.compLeft_hom, Homotopy.compRight_hom,
    Pi.zero_apply, zero_add, add_zero]

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For i∈ℤ∪{⊥,⊤}, this is a chain
homotopy G_i(f)≃G_i(g). It is zero at bottom and every negative finite cut, the transported
finite-stage homotopy at each nonnegative integer cut, and the signed homotopy Tot f≃Tot g at
top. -/
def horizontalCompleteFilteredTotalHomotopy (i : EInt) :
    _root_.Homotopy (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i)
      (horizontalCompleteFilteredTotalComplexMapOfBicomplex g i) := by
  induction i using WithBotTop.rec with
  | bot =>
    change _root_.Homotopy (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
      HomologicalComplex.zero) 0
    exact Homotopy.refl 0
  | coe a =>
    by_cases ha : 0 ≤ a
    · exact horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha
    · have hz : IsZero (horizontalCompleteFilteredTotalComplex K (a : EInt)) := by
        rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a (lt_of_not_ge ha)]
        exact HomologicalComplex.isZero_zero
      exact Homotopy.ofEq (hz.eq_of_src _ _)
  | top =>
    change _root_.Homotopy (total.map f c) (total.map g c)
    exact verticalTotalHomotopy h

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For n,m∈ℕ, the component of the
complete-stage homotopy at i=⊤ equals H_{n,m} of the signed total homotopy Tot f≃Tot g. The top
filtered stages are Tot K and Tot L. -/
@[simp]
theorem horizontalCompleteFilteredTotalHomotopy_hom_top (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h ⊤).hom n m =
      (verticalTotalHomotopy h).hom n m := rfl

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For every n,m∈ℕ, the component of
G_⊥(f)≃G_⊥(g) is zero. Both bottom stages are the zero chain complex. -/
@[simp]
theorem horizontalCompleteFilteredTotalHomotopy_hom_bot (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h ⊥).hom n m = 0 := rfl

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For an integer a<0 and n,m∈ℕ, the
complete-stage homotopy component at cut a is zero. The complete horizontal filtration assigns
the zero chain complex to each such negative finite cut. -/
theorem horizontalCompleteFilteredTotalHomotopy_hom_coe_of_neg (a : ℤ) (ha : a < 0)
    (n m : ℕ) : (horizontalCompleteFilteredTotalHomotopy h (a : EInt)).hom n m = 0 := by
  simp only [horizontalCompleteFilteredTotalHomotopy, WithBotTop.rec_coe,
    dite_eq_right (not_le.mpr ha), Homotopy.ofEq_hom, Pi.zero_apply]

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For a∈ℤ with a≥0 and n,m∈ℕ, the
component of the complete-stage homotopy at cut a equals the component obtained by transporting
H^a:G^fin_a(f)≃G^fin_a(g) through the complete-to-finite stage isomorphisms. The equality
compares these two specified homotopies between G_a(f) and G_a(g). -/
theorem horizontalCompleteFilteredTotalHomotopy_hom_coe_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h (a : EInt)).hom n m =
      (horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha).hom n m := by
  simp only [horizontalCompleteFilteredTotalHomotopy, WithBotTop.rec_coe, dite_eq_left ha]

private theorem completeOfNonneg_toTotal (a : ℤ) (ha : 0 ≤ a) (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal L (a : EInt)).f m =
      (horizontalCompleteFilteredTotalToTotal K (a : EInt)).f n ≫
        (verticalTotalHomotopy h).hom n m := by
  have hL : (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv ≫
      horizontalCompleteFilteredTotalToTotal L (a : EInt) =
        horizontalFilteredTotalComplexToTotal L a.toNat := by
    rw [← horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal L a ha,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hLf := congrArg
    (fun φ : horizontalFilteredTotalComplex L a.toNat ⟶ L.total c => φ.f m) hL
  have hKf := congrArg
    (fun φ : horizontalCompleteFilteredTotalComplex K (a : EInt) ⟶ K.total c => φ.f n)
    (horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha)
  simp only [HomologicalComplex.comp_f] at hLf hKf
  rw [horizontalCompleteFilteredTotalHomotopyOfNonneg_hom]
  calc
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalHomotopy h a.toNat).hom n m ≫
          ((horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv.f m ≫
            (horizontalCompleteFilteredTotalToTotal L (a : EInt)).f m)) := by
      simp only [Category.assoc]
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalHomotopy h a.toNat).hom n m ≫
          (horizontalFilteredTotalComplexToTotal L a.toNat).f m) := by rw [hLf]
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalComplexToTotal K a.toNat).f n ≫
          (verticalTotalHomotopy h).hom n m) := by
      rw [horizontalFilteredTotalHomotopy_toTotal]
    _ = _ := by rw [← Category.assoc, hKf]

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For i∈ℤ∪{⊥,⊤} and n,m∈ℕ, let
H^i:G_i(f)≃G_i(g), H:Tot f≃Tot g, and ι_i^K:G_i(K)→Tot K, ι_i^L:G_i(L)→Tot L be the inclusions.
Then (H^i)_{n,m}≫(ι_i^L)_m=(ι_i^K)_n≫H_{n,m}. -/
@[reassoc]
theorem horizontalCompleteFilteredTotalHomotopy_toTotal (i : EInt) (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h i).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal L i).f m =
      (horizontalCompleteFilteredTotalToTotal K i).f n ≫ (verticalTotalHomotopy h).hom n m := by
  induction i using WithBotTop.rec with
  | bot =>
    rw [horizontalCompleteFilteredTotalHomotopy_hom_bot]
    change 0 ≫ _ = (0 : (HomologicalComplex.zero : ChainComplex C ℕ).X n ⟶ _) ≫ _
    simp
  | coe a =>
    by_cases ha : 0 ≤ a
    · rw [horizontalCompleteFilteredTotalHomotopy_hom_coe_of_nonneg h a ha]
      exact completeOfNonneg_toTotal h a ha n m
    · have hz : IsZero (horizontalCompleteFilteredTotalComplex K (a : EInt)) := by
        rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a (lt_of_not_ge ha)]
        exact HomologicalComplex.isZero_zero
      have hi : horizontalCompleteFilteredTotalToTotal K (a : EInt) = 0 := hz.eq_of_src _ _
      rw [horizontalCompleteFilteredTotalHomotopy_hom_coe_of_neg h a (lt_of_not_ge ha), hi]
      simp
  | top =>
    rw [horizontalCompleteFilteredTotalHomotopy_hom_top]
    change (verticalTotalHomotopy h).hom n m ≫ 𝟙 _ = 𝟙 _ ≫ (verticalTotalHomotopy h).hom n m
    simp

/-- Let C be preadditive with a zero object and finite coproducts and K a bicomplex of shape (down
ℕ,down ℕ). For every complete cut i∈ℤ∪{⊥,⊤} and n∈ℕ, the term map (G_i(K))_n→(Tot K)_n is monic.
At nonnegative finite cuts it is the inclusion of the retained horizontal summands, at top it is
the identity, and at bottom or negative cuts its source is zero. -/
instance horizontalCompleteFilteredTotalToTotal_f_mono (i : EInt) (n : ℕ) :
    Mono ((horizontalCompleteFilteredTotalToTotal K i).f n) := by
  induction i using WithBotTop.rec with
  | bot =>
    change Mono (0 : (HomologicalComplex.zero : ChainComplex C ℕ).X n ⟶ (K.total c).X n)
    infer_instance
  | coe a =>
    by_cases ha : 0 ≤ a
    · have hs := congrArg (fun φ => φ.f n)
        (horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha)
      rw [← hs]
      change Mono ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        (horizontalFilteredTotalComplexToTotal K a.toNat).f n)
      let _ : Mono ((horizontalFilteredTotalComplexToTotal K a.toNat).f n) := by
        change Mono (horizontalFilteredTotalToTotal K a.toNat n)
        infer_instance
      infer_instance
    · have hz : IsZero ((horizontalCompleteFilteredTotalComplex K (a : EInt)).X n) := by
        rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a (lt_of_not_ge ha)]
        exact isZero_zero C
      exact { right_cancellation := fun g h _ => hz.eq_of_tgt g h }
  | top =>
    change Mono (𝟙 ((K.total c).X n))
    infer_instance

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For i≤j in ℤ∪{⊥,⊤} and n,m∈ℕ, write
t^K_{i,j}:G_i(K)→G_j(K) and t^L_{i,j} for the complete-stage transitions, and H^i,H^j for the
stage homotopies. Then (t^K_{i,j})_n≫(H^j)_{n,m}=(H^i)_{n,m}≫(t^L_{i,j})_m. The equality
includes bottom, negative finite and top cuts. -/
theorem horizontalCompleteFilteredTotalHomotopy_naturality
    {i j : EInt} (hij : i ≤ j) (n m : ℕ) :
    (horizontalCompleteFilteredTotalMap K hij).f n ≫
        (horizontalCompleteFilteredTotalHomotopy h j).hom n m =
      (horizontalCompleteFilteredTotalHomotopy h i).hom n m ≫
        (horizontalCompleteFilteredTotalMap L hij).f m := by
  have hK := congrArg
    (fun φ : horizontalCompleteFilteredTotalComplex K i ⟶ K.total c => φ.f n)
    (horizontalCompleteFilteredTotalMap_toTotal K hij)
  have hL := congrArg
    (fun φ : horizontalCompleteFilteredTotalComplex L i ⟶ L.total c => φ.f m)
    (horizontalCompleteFilteredTotalMap_toTotal L hij)
  simp only [HomologicalComplex.comp_f] at hK hL
  apply (cancel_mono ((horizontalCompleteFilteredTotalToTotal L j).f m)).mp
  rw [Category.assoc, horizontalCompleteFilteredTotalHomotopy_toTotal,
    ← Category.assoc, hK, Category.assoc, hL, horizontalCompleteFilteredTotalHomotopy_toTotal]

omit [HasZeroObject C] in
/-- For a first-quadrant bicomplex K in a preadditive category with finite coproducts and k∈ℕ, the
induced map of the finite horizontal stage under id_K is id_{G^fin_k(K)}. Thus
G^fin_k(id_K)=id_{G^fin_k(K)} as chain maps of shape down ℕ. -/
@[simp]
theorem horizontalFilteredTotalComplexMapOfBicomplex_id (k : ℕ) :
    horizontalFilteredTotalComplexMapOfBicomplex (𝟙 K) k =
      𝟙 (horizontalFilteredTotalComplex K k) := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalTotalFilteredObjectFunctor (C := C)).map_id K)
  have hk := congr_app hs k
  change horizontalFilteredTotalComplexMapOfBicomplex (𝟙 K) k = 𝟙 _ at hk
  exact hk

omit [HasZeroObject C] in
/-- Let C be preadditive with finite coproducts, φ:K→L and ψ:L→M morphisms of bicomplexes of shape
(down ℕ,down ℕ), and k∈ℕ. The induced finite-stage maps satisfy
G^fin_k(φ≫ψ)=G^fin_k(φ)≫G^fin_k(ψ). -/
@[simp]
theorem horizontalFilteredTotalComplexMapOfBicomplex_comp
    {M : HomologicalComplex₂ C c c} (φ : K ⟶ L) (ψ : L ⟶ M) (k : ℕ) :
    horizontalFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) k =
      horizontalFilteredTotalComplexMapOfBicomplex φ k ≫
        horizontalFilteredTotalComplexMapOfBicomplex ψ k := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalTotalFilteredObjectFunctor (C := C)).map_comp φ ψ)
  have hk := congr_app hs k
  change horizontalFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) k =
    horizontalFilteredTotalComplexMapOfBicomplex φ k ≫
      horizontalFilteredTotalComplexMapOfBicomplex ψ k at hk
  exact hk

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts and i∈ℤ∪{⊥,⊤}, the complete-stage map induced by id_K is id_{G_i(K)}. The formula
includes the zero bottom and negative stages and the full total complex at top. -/
@[simp]
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_id (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex (𝟙 K) i =
      𝟙 (horizontalCompleteFilteredTotalComplex K i) := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalCompleteTotalFilteredObjectFunctor (C := C)).map_id K)
  have hi := congr_app hs i
  change horizontalCompleteFilteredTotalComplexMapOfBicomplex (𝟙 K) i = 𝟙 _ at hi
  exact hi

/-- Let C be preadditive with a zero object and finite coproducts, φ:K→L and ψ:L→M morphisms of
bicomplexes of shape (down ℕ,down ℕ), and i∈ℤ∪{⊥,⊤}. The complete-stage maps satisfy
G_i(φ≫ψ)=G_i(φ)≫G_i(ψ) at every complete cut. -/
@[simp]
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp
    {M : HomologicalComplex₂ C c c} (φ : K ⟶ L) (ψ : L ⟶ M) (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex φ i ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex ψ i := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalCompleteTotalFilteredObjectFunctor (C := C)).map_comp φ ψ)
  have hi := congr_app hs i
  change horizontalCompleteFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) i =
    horizontalCompleteFilteredTotalComplexMapOfBicomplex φ i ≫
      horizontalCompleteFilteredTotalComplexMapOfBicomplex ψ i at hi
  exact hi

end HomologicalComplex₂

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K₀ K₁ L₀ L₁ : CochainComplex C ℤ}
  (uK : K₀ ⟶ K₁) (uL : L₀ ⟶ L₁)
  {f₀ g₀ : K₀ ⟶ L₀} {f₁ g₁ : K₁ ⟶ L₁}
  (h₀ : _root_.Homotopy f₀ g₀) (h₁ : _root_.Homotopy f₁ g₁)

/-- Let C be preadditive with binary biproducts, u_K:K₀→K₁ and u_L:L₀→L₁ maps of integer-indexed
cochain complexes, h₀ a homotopy f₀≃g₀ from K₀ to L₀ and h₁ a homotopy f₁≃g₁ from K₁ to L₁. For
n,m∈ℤ, identify Cone(u_K)^n with K₀^{n+1}⊕K₁^n and Cone(u_L)^m with L₀^{m+1}⊕L₁^m. This
component is the diagonal map diag(-h₀_{n+1,m+1},h₁_{n,m}) between those biproducts, transported
through the canonical cone-coordinate isomorphisms. No compatibility square is required to
define this component. -/
def mapCompatibleHomotopyHom (n m : ℤ) :
    (CochainComplex.mappingCone uK).X n ⟶ (CochainComplex.mappingCone uL).X m :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod uK n (n + 1) rfl).hom ≫
    biprod.map (-(h₀.hom (n + 1) (m + 1))) (h₁.hom n m) ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod uL m (m + 1) rfl).inv

/-- Let C be preadditive with binary biproducts, u_K:K₀→K₁ and u_L:L₀→L₁ maps of integer-indexed
cochain complexes, h₀ a homotopy f₀≃g₀ from K₀ to L₀ and h₁ a homotopy f₁≃g₁ from K₁ to L₁. Let
H_{n,m}:Cone(u_K)^n→Cone(u_L)^m be the diagonal component diag(-h₀_{n+1,m+1},h₁_{n,m}). If
j_K:K₀^{n+1}→Cone(u_K)^n and j_L:L₀^{m+1}→Cone(u_L)^m are lower-coordinate inclusions, then
j_K≫H_{n,m}=(-h₀_{n+1,m+1})≫j_L. -/
@[reassoc]
theorem mapCompatibleHomotopyHom_inl (n m : ℤ) :
    (inl uK).v (n + 1) n (by omega) ≫ mapCompatibleHomotopyHom uK uL h₀ h₁ n m =
      -(h₀.hom (n + 1) (m + 1)) ≫ (inl uL).v (m + 1) m (by omega) := by
  simp [mapCompatibleHomotopyHom, inl]

/-- Let C be preadditive with binary biproducts, u_K:K₀→K₁ and u_L:L₀→L₁ maps of integer-indexed
cochain complexes, h₀ a homotopy f₀≃g₀ from K₀ to L₀ and h₁ a homotopy f₁≃g₁ from K₁ to L₁. For
n,m∈ℤ, let H_{n,m}:Cone(u_K)^n→Cone(u_L)^m be diag(-h₀_{n+1,m+1},h₁_{n,m}). If
j_K:K₁^n→Cone(u_K)^n and j_L:L₁^m→Cone(u_L)^m are upper-coordinate inclusions, then
j_K≫H_{n,m}=h₁_{n,m}≫j_L. -/
@[reassoc]
theorem mapCompatibleHomotopyHom_inr (n m : ℤ) :
    (inr uK).f n ≫ mapCompatibleHomotopyHom uK uL h₀ h₁ n m =
      h₁.hom n m ≫ (inr uL).f m := by
  simp [mapCompatibleHomotopyHom, inr]

/-- Let C be preadditive with binary biproducts, u_K:K₀→K₁ and u_L:L₀→L₁ maps of integer-indexed
cochain complexes, h₀ a homotopy f₀≃g₀ from K₀ to L₀ and h₁ a homotopy f₁≃g₁ from K₁ to L₁. For
n,m∈ℤ with m+1≠n, the diagonal cone component H_{n,m}=diag(-h₀_{n+1,m+1},h₁_{n,m}) is zero. Both
component homotopies lower cochain degree by one, so the same vanishing condition holds after
shifting the lower coordinate. -/
theorem mapCompatibleHomotopyHom_zero (n m : ℤ)
    (hrel : ¬(ComplexShape.up ℤ).Rel m n) :
    mapCompatibleHomotopyHom uK uL h₀ h₁ n m = 0 := by
  have hshift : ¬(ComplexShape.up ℤ).Rel (m + 1) (n + 1) := by
    intro hs
    apply hrel
    change m + 1 = n
    change (m + 1) + 1 = n + 1 at hs
    omega
  have hz : biprod.map (0 : K₀.X (n + 1) ⟶ L₀.X (m + 1))
      (0 : K₁.X n ⟶ L₁.X m) = 0 := by
    ext <;> simp
  simp only [mapCompatibleHomotopyHom, h₀.zero (n + 1) (m + 1) hshift,
    h₁.zero n m hrel, neg_zero, hz, zero_comp, comp_zero]

private theorem inl_map_f (a : K₀ ⟶ L₀) (b : K₁ ⟶ L₁)
    (hc : uK ≫ b = a ≫ uL) (n : ℤ) :
    (inl uK).v (n + 1) n (by omega) ≫ (map uK uL a b hc).f n =
      a.f (n + 1) ≫ (inl uL).v (n + 1) n (by omega) := by
  simp [map]

private theorem inr_map_f (a : K₀ ⟶ L₀) (b : K₁ ⟶ L₁)
    (hc : uK ≫ b = a ≫ uL) (n : ℤ) :
    (inr uK).f n ≫ (map uK uL a b hc).f n = b.f n ≫ (inr uL).f n := by
  simp [map]

@[reassoc]
private theorem inl_hom_with_indices (n m i j : ℤ) (hi : n + 1 = i) (hj : m + 1 = j) :
    (inl uK).v i n (by omega) ≫ mapCompatibleHomotopyHom uK uL h₀ h₁ n m =
      -(h₀.hom i j) ≫ (inl uL).v j m (by omega) := by
  subst i
  subst j
  exact mapCompatibleHomotopyHom_inl uK uL h₀ h₁ n m

/-- Let C be preadditive with binary biproducts, u_K:K₀→K₁ and u_L:L₀→L₁ maps of integer-indexed
cochain complexes, h₀ a homotopy f₀≃g₀ from K₀ to L₀ and h₁ a homotopy f₁≃g₁ from K₁ to L₁.
Assume u_K≫f₁=f₀≫u_L and u_K≫g₁=g₀≫u_L. Also assume the componentwise compatibility
u_K^n≫h₁_{n,m}=h₀_{n,m}≫u_L^m for every n,m∈ℤ. The induced cone maps Cone(f₀,f₁) and Cone(g₀,g₁)
are homotopic, with components diag(-h₀_{n+1,m+1},h₁_{n,m}) under the cone biproduct
coordinates. The strict compatibility makes the off-diagonal homotopy term vanish. -/
def mapHomotopyOfCompatible
    (hf : uK ≫ f₁ = f₀ ≫ uL) (hg : uK ≫ g₁ = g₀ ≫ uL)
    (hn : ∀ n m, uK.f n ≫ h₁.hom n m = h₀.hom n m ≫ uL.f m) :
    _root_.Homotopy (map uK uL f₀ f₁ hf) (map uK uL g₀ g₁ hg) where
  hom := mapCompatibleHomotopyHom uK uL h₀ h₁
  zero n m hrel := mapCompatibleHomotopyHom_zero uK uL h₀ h₁ n m hrel
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from by change n - 1 + 1 = n; omega)]
    apply ext_from uK (n + 1) n rfl
    · have he := h₀.comm (n + 1)
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n + 1) ((n + 1) + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)] at he
      have hsub : n - 1 + 1 = n := by omega
      have hhnext := mapCompatibleHomotopyHom_inl uK uL h₀ h₁ (n + 1) n
      simp only [Preadditive.comp_add]
      rw [inl_map_f uK uL f₀ f₁ hf n, inl_map_f uK uL g₀ g₁ hg n,
        inl_v_d_assoc uK (n + 1) n ((n + 1) + 1) (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [mapCompatibleHomotopyHom_inr, hhnext,
        inl_hom_with_indices_assoc uK uL h₀ h₁ n (n - 1) (n + 1) n rfl hsub]
      simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
      rw [inl_v_d uL n (n - 1) (n + 1) (by omega) (by omega)]
      simp only [Preadditive.comp_sub]
      have hn' : uK.f (n + 1) ≫ (h₁.hom (n + 1) n ≫ (inr uL).f n) =
          h₀.hom (n + 1) n ≫ (uL.f n ≫ (inr uL).f n) := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ (inr uL).f n) (hn (n + 1) n)
      rw [hn', he]
      simp only [Preadditive.add_comp, Category.assoc]
      abel
    · have he := h₁.comm n
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from
          by change n - 1 + 1 = n; omega)] at he
      simp only [Preadditive.comp_add]
      rw [inr_map_f uK uL f₀ f₁ hf n, inr_map_f uK uL g₀ g₁ hg n,
        inr_f_d_assoc, mapCompatibleHomotopyHom_inr,
        mapCompatibleHomotopyHom_inr_assoc, inr_f_d]
      rw [he]
      simp only [Preadditive.add_comp, Category.assoc]

end CochainComplex.mappingCone

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  {f g : K ⟶ L}
  (h : _root_.Homotopy (flipMap f) (flipMap g))

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. Let F_i(K) be G_i(K) reindexed by
chain degree r↦cochain degree -r and extended by zero. At each i∈ℤ∪{⊥,⊤}, the complete-stage
chain homotopy extends to a cochain homotopy F_i(f)≃F_i(g). Its nonzero components lower cochain
degree by one. -/
def horizontalCompleteFiltrationCochainHomotopy (i : EInt) :
    _root_.Homotopy ((horizontalCompleteFiltrationCochainDiagramNatTrans f).app i)
      ((horizontalCompleteFiltrationCochainDiagramNatTrans g).app i) :=
  (horizontalCompleteFilteredTotalHomotopy h i).extend ComplexShape.embeddingDownNat

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. Let F_i(K) denote the integer cochain
extension of G_i(K), and H^i:F_i(f)≃F_i(g) its extended homotopy. For an index arrow a:i→j and
n,m∈ℤ, the cochain transition maps satisfy (F(K)(a))^n≫(H^j)_{n,m}=(H^i)_{n,m}≫(F(L)(a))^m. -/
theorem horizontalCompleteFiltrationCochainHomotopy_naturality
    {i j : EInt} (a : i ⟶ j) (n m : ℤ) :
    ((horizontalCompleteFiltrationCochainDiagram K).map a).f n ≫
        (horizontalCompleteFiltrationCochainHomotopy h j).hom n m =
      (horizontalCompleteFiltrationCochainHomotopy h i).hom n m ≫
        ((horizontalCompleteFiltrationCochainDiagram L).map a).f m := by
  have ha : homOfLE (leOfHom a) = a := Subsingleton.elim _ _
  rw [← ha]
  change (HomologicalComplex.extendMap (horizontalCompleteFilteredTotalMap K (leOfHom a))
      ComplexShape.embeddingDownNat).f n ≫
      ((horizontalCompleteFilteredTotalHomotopy h j).extend
        ComplexShape.embeddingDownNat).hom n m =
    ((horizontalCompleteFilteredTotalHomotopy h i).extend
      ComplexShape.embeddingDownNat).hom n m ≫
      (HomologicalComplex.extendMap (horizontalCompleteFilteredTotalMap L (leOfHom a))
        ComplexShape.embeddingDownNat).f m
  exact _root_.Homotopy.extend_hom_naturality
    (horizontalCompleteFilteredTotalHomotopy h i)
    (horizontalCompleteFilteredTotalHomotopy h j)
    (horizontalCompleteFilteredTotalMap K (leOfHom a))
    (horizontalCompleteFilteredTotalMap L (leOfHom a))
    (horizontalCompleteFilteredTotalHomotopy_naturality h (leOfHom a))
    ComplexShape.embeddingDownNat n m

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For an interval I=(i→j) of ℤ∪{⊥,⊤},
write F_i,F_j for the integer cochain filtration stages. The maps induced by f and g from
Cone(F_i(K)→F_j(K)) to Cone(F_i(L)→F_j(L)) are homotopic. The cone homotopy uses the negative
shifted homotopy of the lower stage i and the unshifted homotopy of the upper stage j; their
strict compatibility follows from naturality of the stage homotopies. -/
def horizontalCompleteFiltrationMappingConeHomotopy (I : ComposableArrows EInt 1) :
    _root_.Homotopy ((horizontalCompleteFiltrationMappingConeNatTrans f).app I)
      ((horizontalCompleteFiltrationMappingConeNatTrans g).app I) :=
  CochainComplex.mappingCone.mapHomotopyOfCompatible
    ((horizontalCompleteFiltrationCochainDiagram K).map (I.map' 0 1))
    ((horizontalCompleteFiltrationCochainDiagram L).map (I.map' 0 1))
    (horizontalCompleteFiltrationCochainHomotopy h (I.obj 0))
    (horizontalCompleteFiltrationCochainHomotopy h (I.obj 1))
    ((horizontalCompleteFiltrationCochainDiagramNatTrans f).naturality (I.map' 0 1))
    ((horizontalCompleteFiltrationCochainDiagramNatTrans g).naturality (I.map' 0 1))
    (horizontalCompleteFiltrationCochainHomotopy_naturality h (I.map' 0 1))

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For an interval I=(i→j) and n,m∈ℤ,
let H^I be the induced relative-cone homotopy and H^i the extended cochain homotopy of the lower
stage. For the lower inclusions J_K:F_i(K)^{n+1}→Cone_I(K)^n and J_L:F_i(L)^{m+1}→Cone_I(L)^m,
J_K≫(H^I)_{n,m}=(-(H^i)_{n+1,m+1})≫J_L. -/
@[reassoc]
theorem horizontalCompleteFiltrationMappingConeHomotopy_inl
    (I : ComposableArrows EInt 1) (n m : ℤ) :
    (CochainComplex.mappingCone.inl
        ((horizontalCompleteFiltrationCochainDiagram K).map (I.map' 0 1))).v
          (n + 1) n (by omega) ≫
        (horizontalCompleteFiltrationMappingConeHomotopy h I).hom n m =
      -((horizontalCompleteFiltrationCochainHomotopy h (I.obj 0)).hom (n + 1) (m + 1)) ≫
        (CochainComplex.mappingCone.inl
          ((horizontalCompleteFiltrationCochainDiagram L).map (I.map' 0 1))).v
            (m + 1) m (by omega) :=
  CochainComplex.mappingCone.mapCompatibleHomotopyHom_inl _ _ _ _ n m

/-- Let C be preadditive with a zero object and finite coproducts, K,L bicomplexes of shape (down
ℕ,down ℕ), f,g:K→L and h a homotopy from flip f to flip g. For an interval I=(i→j) and n,m∈ℤ,
let H^I be the relative-cone homotopy and H^j the extended cochain homotopy of the upper stage.
With upper inclusions J_K:F_j(K)^n→Cone_I(K)^n and J_L:F_j(L)^m→Cone_I(L)^m,
J_K≫(H^I)_{n,m}=(H^j)_{n,m}≫J_L. -/
@[reassoc]
theorem horizontalCompleteFiltrationMappingConeHomotopy_inr
    (I : ComposableArrows EInt 1) (n m : ℤ) :
    (CochainComplex.mappingCone.inr
        ((horizontalCompleteFiltrationCochainDiagram K).map (I.map' 0 1))).f n ≫
        (horizontalCompleteFiltrationMappingConeHomotopy h I).hom n m =
      (horizontalCompleteFiltrationCochainHomotopy h (I.obj 1)).hom n m ≫
        (CochainComplex.mappingCone.inr
          ((horizontalCompleteFiltrationCochainDiagram L).map (I.map' 0 1))).f m :=
  CochainComplex.mappingCone.mapCompatibleHomotopyHom_inr _ _ _ _ n m

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts and an interval I=(i→j) in ℤ∪{⊥,⊤}, the map on Cone(F_i(K)→F_j(K)) induced by id_K is
the identity. Here F is the complete horizontal chain filtration extended to cochain degrees by
r↦-r. -/
theorem horizontalCompleteFiltrationMappingConeNatTrans_id
    (I : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationMappingConeNatTrans (𝟙 K)).app I =
      𝟙 ((horizontalCompleteFiltrationMappingConeFunctor K).obj I) := by
  simp only [horizontalCompleteFiltrationMappingConeNatTrans_app,
    horizontalCompleteFiltrationCochainDiagramNatTrans_app,
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_id, HomologicalComplex.extendMap_id]
  exact CochainComplex.mappingCone.map_id _

/-- Let C be preadditive with a zero object and finite coproducts, φ:K→L and ψ:L→M morphisms of
first-quadrant bicomplexes and I=(i→j) an extended-integer interval. For the cochain filtration
F, let c_I(φ) be the induced map Cone(F_i(K)→F_j(K))→Cone(F_i(L)→F_j(L)). Then
c_I(φ≫ψ)=c_I(φ)≫c_I(ψ). -/
theorem horizontalCompleteFiltrationMappingConeNatTrans_comp
    {M : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (φ : K ⟶ L) (ψ : L ⟶ M) (I : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationMappingConeNatTrans (φ ≫ ψ)).app I =
      (horizontalCompleteFiltrationMappingConeNatTrans φ).app I ≫
        (horizontalCompleteFiltrationMappingConeNatTrans ψ).app I := by
  simp only [horizontalCompleteFiltrationMappingConeNatTrans_app,
    horizontalCompleteFiltrationCochainDiagramNatTrans_app,
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp, HomologicalComplex.extendMap_comp]
  apply CochainComplex.mappingCone.map_comp

end HomologicalComplex₂
