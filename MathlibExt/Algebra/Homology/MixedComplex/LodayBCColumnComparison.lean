/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.MixedComplex.LodayBCColumnSigns

/-!
# BC coordinates for a mixed Connes bicomplex

Let C be preadditive with a zero object and M a mixed complex. Its p-th Connes column has stored
vertical differential (-1)^p b in supported cells. The signed row removes that column factor,
giving a column with unsigned b.

Multiplying the signed-row isomorphism by the constant triangular unit c_p gives U_p with cell
sign s_{p,q}=c_p(-1)^{pq}. Define horizontal arrows by U_{p+1} followed by the Connes horizontal
map and U_p⁻¹. These arrows form a bicomplex, and the U_p give its isomorphism to the Connes
bicomplex.

If C has finite coproducts, totalization on the finite diagonals p+q=n carries this isomorphism
to a total-complex isomorphism. Every cell injection is transported by the same cell sign.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive HomologicalComplex HomologicalComplex₂

universe u v

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasZeroObject C]
  (M : MixedComplex C)

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. For p∈ℕ, the BC column is the signed row of C_can at p. In each
supported cell it has the same coefficient M_{q-p}, and its vertical differential is b because
the extra (-1)^p cancels the stored Connes column sign. -/
abbrev lodayBCColumn (p : ℕ) : ChainComplex C ℕ := M.connesBicomplex.signedRow p


/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. The isomorphism U_p from the signed row to C_can(p) is c_p times the signed-row
comparison. Its forward and inverse degree-q entries are both s_{p,q}•id. -/
def lodayBCColumnIso (p : ℕ) : M.lodayBCColumn p ≅ M.connesBicomplex.X p where
  hom := lodayColumnSign p • (M.connesBicomplex.signedRowIso p).hom
  inv := (lodayColumnSign p)⁻¹ • (M.connesBicomplex.signedRowIso p).inv
  hom_inv_id := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, mul_inv_cancel,
      one_smul, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, inv_mul_cancel,
      one_smul, Iso.inv_hom_id]

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. For
every p,q∈ℕ, (U_p.hom)_q=s_{p,q}•id_{C_can(p,q)}. This includes both the triangular and
row-parity factors. -/
@[simp]
theorem lodayBCColumnIso_hom_f (p q : ℕ) :
    (M.lodayBCColumnIso p).hom.f q = lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q) := by
  change lodayColumnSign p •
      (((ComplexShape.down ℕ).ε p) ^ q • 𝟙 ((M.connesBicomplex.X p).X q)) = _
  rw [smul_smul]
  rfl

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. For
every p,q∈ℕ, (U_p.inv)_q=s_{p,q}•id_{C_can(p,q)}, using s_{p,q}²=1. -/
@[simp]
theorem lodayBCColumnIso_inv_f (p q : ℕ) :
    (M.lodayBCColumnIso p).inv.f q = lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q) := by
  change (lodayColumnSign p)⁻¹ •
      ((((ComplexShape.down ℕ).ε p) ^ q)⁻¹ • 𝟙 ((M.connesBicomplex.X p).X q)) = _
  have he : ((((ComplexShape.down ℕ).ε p) ^ q)⁻¹) = ((ComplexShape.down ℕ).ε p) ^ q := by
    apply (mul_left_cancel (a := ((ComplexShape.down ℕ).ε p) ^ q))
    rw [mul_inv_cancel]
    rw [ComplexShape.ε_down_ℕ, ← pow_mul]
    rw [← pow_add]
    exact (show Even (p * q + p * q) from ⟨p * q, rfl⟩).neg_one_pow |>.symm
  rw [lodayColumnSign_inv, he, smul_smul]
  rfl

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. For
p∈ℕ, d^BC_{p+1,p}=U_{p+1}.hom≫d^can_{p+1,p}≫U_p.inv is a column chain map C_BC(p+1)→C_BC(p). -/
def lodayBCHorizontal (p : ℕ) : M.lodayBCColumn (p + 1) ⟶ M.lodayBCColumn p :=
  (M.lodayBCColumnIso (p + 1)).hom ≫ M.connesBicomplex.d (p + 1) p ≫
    (M.lodayBCColumnIso p).inv

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. For
p∈ℕ, d^BC_{p+2,p+1}≫d^BC_{p+1,p}=0. The intermediate U_{p+1} inverse and forward maps cancel,
leaving the Connes bicomplex zero-composite equation. -/
theorem lodayBCHorizontal_squared (p : ℕ) :
    M.lodayBCHorizontal (p + 1) ≫ M.lodayBCHorizontal p = 0 := by
  simp only [lodayBCHorizontal, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc (M.connesBicomplex.d (p + 2) (p + 1))
    (M.connesBicomplex.d (p + 1) p)]
  rw [HomologicalComplex.d_comp_d, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. The down–down bicomplex C_BC has p-th column equal to the signed Connes row and
horizontal differential U_{p+1}.hom≫d^can≫U_p.inv. Its coefficients and both nonnegative indices
are retained. -/
def lodayBCBicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of M.lodayBCColumn M.lodayBCHorizontal M.lodayBCHorizontal_squared


/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. The
column isomorphisms U_p assemble to C_BC≅C_can. Their definition of the horizontal maps ensures
the horizontal chain squares commute. -/
def lodayBCBicomplexIso : M.lodayBCBicomplex ≅ M.connesBicomplex :=
  HomologicalComplex.Hom.isoOfComponents M.lodayBCColumnIso (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    dsimp only [lodayBCBicomplex]
    rw [ChainComplex.of_d]
    simp only [lodayBCHorizontal, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. The
forward bicomplex isomorphism has (p,q)-entry s_{p,q}•id_{C_can(p,q)} for all p,q∈ℕ. -/
@[simp]
theorem lodayBCBicomplexIso_hom_f_f (p q : ℕ) :
    ((M.lodayBCBicomplexIso.hom).f p).f q =
      lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q) :=
  M.lodayBCColumnIso_hom_f p q

section Total

variable [CategoryTheory.Limits.HasFiniteCoproducts C]

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id.
Assume C has finite coproducts. Totalization gives V:Tot(C_BC)≅Tot(C_can) as nonnegative chain
complexes, using the finite fibre p+q=n in degree n. -/
def lodayBCTotalIso : M.lodayBCBicomplex.total (ComplexShape.down ℕ) ≅
    M.connesBicomplex.total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.mapIso M.lodayBCBicomplexIso (ComplexShape.down ℕ)

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Write C_can for
the Connes bicomplex of M. Put c₀=1, c_{p+1}=c_p(-1)^p, and s_{p,q}=c_p(-1)^{pq}, as integer
units. Write C_can for the Connes bicomplex, and C_BC for the bicomplex whose p-th column is its
signed row. The column isomorphism U_p:C_BC(p)≅C_can(p) has degree-q component s_{p,q}•id. With
finite coproducts, for p,q,n∈ℕ and p+q=n, ι^BC_{p,q,n}≫V_n=s_{p,q}•id≫ι^can_{p,q,n}. Thus the
total isomorphism retains the full sign on each summand. -/
@[reassoc]
theorem lodayBCTotalIso_ι (p q n : ℕ) (h : p + q = n) :
    M.lodayBCBicomplex.ιTotal (ComplexShape.down ℕ) p q n h ≫ M.lodayBCTotalIso.hom.f n =
      (lodayCellSign p q • 𝟙 ((M.connesBicomplex.X p).X q)) ≫
        M.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q n h := by
  change M.lodayBCBicomplex.ιTotal (ComplexShape.down ℕ) p q n h ≫
      (HomologicalComplex₂.total.map M.lodayBCBicomplexIso.hom (ComplexShape.down ℕ)).f n = _
  exact (HomologicalComplex₂.ιTotal_map M.lodayBCBicomplex M.connesBicomplex
      M.lodayBCBicomplexIso.hom (ComplexShape.down ℕ) p q n h).trans
    (congrArg (fun f => f ≫ M.connesBicomplex.ιTotal (ComplexShape.down ℕ) p q n h)
      (M.lodayBCBicomplexIso_hom_f_f p q))

end Total

end MixedComplex
