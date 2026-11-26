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

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Explicit third group cohomology

Let k be a commutative ring, G a group, and A a k-linear representation in universe u. The
degree-three and degree-four inhomogeneous cochains are functions G³→A and G⁴→A. Their
differential is δ₃z(g,h,i,j)=ρ(g)z(h,i,j)-z(gh,i,j)+z(g,hi,j)-z(g,h,ij)+z(g,h,i).

The degree-three short complex is C²(G,A) --δ₂→ C³(G,A) --δ₃→ C⁴(G,A), with
δ₂b(g,h,i)=ρ(g)b(h,i)-b(gh,i)+b(g,hi)-b(g,h). It has cocycles Z³=ker(δ₃) and coboundaries
B³=im(δ₂). Coordinate isomorphisms identify this short complex with the degree-three short
complex of the inhomogeneous cochain complex.

The class map Z³→H³(G,A) is surjective, and two cocycles define the same class exactly when
their difference lies in B³.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Representation

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G)

/-- For a type G in universe u, evaluation at the three indices gives an equivalence (Fin
3→G)≃G×G×G. It sends a tuple function x to (x(0),x(1),x(2)), with the product associated as
G×(G×G). -/
def finThreeEquiv : (Fin 3 → G) ≃ G × G × G :=
  (Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G))

/-- For a type G in universe u, evaluation gives an equivalence (Fin 4→G)≃G×G×G×G. It sends x to
(x(0),x(1),x(2),x(3)), with products associated to the right, and its inverse restores the same
four coordinates. -/
def finFourEquiv : (Fin 4 → G) ≃ G × G × G × G :=
  (Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (finThreeEquiv (G := G)))

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The degree-four term K⁴ of the inhomogeneous complex is isomorphic as a k-module to functions
G⁴→A. The coordinate isomorphism evaluates a Fin 4-indexed group tuple in the order (g,h,i,j),
preserving all four arguments. -/
def cochainsIso₄ : (inhomogeneousCochains A).X 4 ≅
    ModuleCat.of k (G × G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A (finFourEquiv (G := G))).toModuleIso.symm

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The k-linear map δ₃:C³(G,A)→C⁴(G,A) acts on triple-variable functions by
δ₃z(g,h,i,j)=ρ(g)z(h,i,j)-z(gh,i,j)+z(g,hi,j)-z(g,h,ij)+z(g,h,i). The signs are +,-,+,-,+ in
this order. -/
@[simps!]
def d₃₄ : ModuleCat.of k (G × G × G → A) ⟶
    ModuleCat.of k (G × G × G × G → A) :=
  ModuleCat.ofHom
  { toFun := fun f g =>
      A.ρ g.1 (f (g.2.1, g.2.2.1, g.2.2.2)) -
        f (g.1 * g.2.1, g.2.2.1, g.2.2.2) +
        f (g.1, g.2.1 * g.2.2.1, g.2.2.2) -
        f (g.1, g.2.1, g.2.2.1 * g.2.2.2) +
        f (g.1, g.2.1, g.2.2.1)
    map_add' := fun x y => funext fun g => by
      dsimp
      rw [map_add]
      abel
    map_smul' := fun r x => funext fun g => by
      dsimp
      simp only [map_smul, smul_add, smul_sub] }

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Let K be the inhomogeneous cochain complex and e₃:K³≅C³(G,A), e₄:K⁴≅C⁴(G,A) the
tuple-coordinate isomorphisms. Then e₃.hom≫δ₃=K.d_{3,4}≫e₄.hom. The differential is
δ₃z(g,h,i,j)=ρ(g)z(h,i,j)-z(gh,i,j)+z(g,hi,j)-z(g,h,ij)+z(g,h,i). -/
theorem comp_d₃₄_eq :
    (cochainsIso₃ A).hom ≫ d₃₄ A =
      (inhomogeneousCochains A).d 3 4 ≫ (cochainsIso₄ A).hom := by
  ext x y
  let v : Fin 4 → G := (finFourEquiv (G := G)).symm y
  have htail : (fun i : Fin 3 =>
      (Fin.cons y.2.1
        (Fin.cons y.2.2.1
          (Fin.cons y.2.2.2 (finZeroElim : Fin 0 → G))) : Fin 3 → G) i) =
      (finThreeEquiv (G := G)).symm y.2 := by
    funext i
    fin_cases i <;> rfl
  have h0 : Fin.contractNth 0 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1 * y.2.1, y.2.2.1, y.2.2.2) := by
    funext i
    fin_cases i <;> rfl
  have h1 : Fin.contractNth 1 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1, y.2.1 * y.2.2.1, y.2.2.2) := by
    funext i
    fin_cases i <;> rfl
  have h2 : Fin.contractNth 2 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1, y.2.1, y.2.2.1 * y.2.2.2) := by
    funext i
    fin_cases i <;> rfl
  have h3 : Fin.contractNth 3 (fun a b : G => a * b) v =
      (finThreeEquiv (G := G)).symm
        (y.1, y.2.1, y.2.2.1) := by
    funext i
    fin_cases i <;> rfl
  change A.ρ y.1 (x _) - x _ + x _ - x _ + x _ = _ + _
  dsimp [cochainsIso₄, finFourEquiv, finThreeEquiv]
  rw [Fin.sum_univ_four]
  norm_num [sub_eq_add_neg]
  change _ = A.ρ y.1
      (x (fun i : Fin 3 =>
        (Fin.cons y.2.1
          (Fin.cons y.2.2.1
            (Fin.cons y.2.2.2 (finZeroElim : Fin 0 → G))) : Fin 3 → G) i)) +
      (-x (Fin.contractNth 0 (fun a b : G => a * b) v) +
        x (Fin.contractNth 1 (fun a b : G => a * b) v) +
        -x (Fin.contractNth 2 (fun a b : G => a * b) v) +
        x (Fin.contractNth 3 (fun a b : G => a * b) v))
  rw [htail, h0, h1, h2, h3]
  abel

@[reassoc, elementwise]
theorem eq_d₃₄_comp_inv :
    (cochainsIso₃ A).inv ≫ (inhomogeneousCochains A).d 3 4 =
      d₃₄ A ≫ (cochainsIso₄ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₃₄_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem d₂₃_comp_d₃₄ : d₂₃ A ≫ d₃₄ A = 0 := by
  ext f g
  simp [d₂₃, d₃₄, mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

open ShortComplex

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The short complex C²(G,A) --δ₂→ C³(G,A) --δ₃→ C⁴(G,A) computes degree-three cohomology, and
δ₂≫δ₃=0. For b:G×G→A, δ₂b(g,h,i)=ρ(g)b(h,i)-b(gh,i)+b(g,hi)-b(g,h). The differential is
δ₃z(g,h,i,j)=ρ(g)z(h,i,j)-z(gh,i,j)+z(g,hi,j)-z(g,h,ij)+z(g,h,i). -/
@[simps! -isSimp f g]
def shortComplexH3 : ShortComplex (ModuleCat k) :=
  mk (d₂₃ A) (d₃₄ A) (d₂₃_comp_d₃₄ A)

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The submodule Z³(G,A)⊆(G³→A) is ker(δ₃), consisting of functions z with δ₃z(g,h,i,j)=0 for
all g,h,i,j. The differential is
δ₃z(g,h,i,j)=ρ(g)z(h,i,j)-z(gh,i,j)+z(g,hi,j)-z(g,h,ij)+z(g,h,i). -/
def cocycles₃ : Submodule k (G × G × G → A) :=
  LinearMap.ker (d₃₄ A).hom

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The submodule B³(G,A)⊆(G³→A) is im(δ₂), so a three-cochain z lies in it exactly when z=δ₂b
for some b:G²→A. For b:G×G→A, δ₂b(g,h,i)=ρ(g)b(h,i)-b(gh,i)+b(g,hi)-b(g,h). -/
def coboundaries₃ : Submodule k (G × G × G → A) :=
  LinearMap.range (d₂₃ A).hom

variable {A}

@[macro_inline]
instance : FunLike (cocycles₃ A) (G × G × G) A :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem cocycles₃.coe_mk (f : G × G × G → A) (hf) :
    ((⟨f, hf⟩ : cocycles₃ A) : G × G × G → A) = f := rfl

@[simp]
theorem cocycles₃.val_eq_coe (f : cocycles₃ A) : f.1 = f := rfl

@[ext]
theorem cocycles₃_ext {f₁ f₂ : cocycles₃ A}
    (hEq : ∀ g h j : G, f₁ (g, h, j) = f₂ (g, h, j)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ fun p => hEq p.1 p.2.1 p.2.2

theorem mem_cocycles₃_def (f : G × G × G → A) :
    f ∈ cocycles₃ A ↔ ∀ g h i j : G,
      A.ρ g (f (h, i, j)) - f (g * h, i, j) +
        f (g, h * i, j) - f (g, h, i * j) + f (g, h, i) = 0 :=
  LinearMap.mem_ker.trans <| by
    simp_rw [funext_iff, d₃₄_hom_apply, Prod.forall]
    rfl

theorem d₂₃_apply_mem_cocycles₃ (x : G × G → A) :
    d₂₃ A x ∈ cocycles₃ A :=
  d₂₃_comp_d₃₄_apply _ _

@[simp]
theorem cocycles₃.d₃₄_apply (x : cocycles₃ A) : d₃₄ A x = 0 := x.2

@[macro_inline]
instance : FunLike (coboundaries₃ A) (G × G × G) A :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem coboundaries₃.coe_mk (f : G × G × G → A) (hf) :
    ((⟨f, hf⟩ : coboundaries₃ A) : G × G × G → A) = f := rfl

@[simp]
theorem coboundaries₃.val_eq_coe (f : coboundaries₃ A) : f.1 = f := rfl

@[ext]
theorem coboundaries₃_ext {f₁ f₂ : coboundaries₃ A}
    (hEq : ∀ g h j : G, f₁ (g, h, j) = f₂ (g, h, j)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ fun p => hEq p.1 p.2.1 p.2.2

lemma coboundaries₃_le_cocycles₃ (A : Rep k G) :
    coboundaries₃ A ≤ cocycles₃ A := by
  rintro _ ⟨x, rfl⟩
  exact d₂₃_apply_mem_cocycles₃ x

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Since δ₂≫δ₃=0, the submodule B³(G,A)=im(δ₂) lies in Z³(G,A)=ker(δ₃). The inclusion B³→Z³ is
k-linear and sends each coboundary to the cocycle represented by the same function G³→A. -/
abbrev coboundariesToCocycles₃ (A : Rep k G) :
    coboundaries₃ A →ₗ[k] cocycles₃ A :=
  Submodule.inclusion (coboundaries₃_le_cocycles₃ A)

variable (A)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For the inhomogeneous complex K, its degree-three short complex K²→K³→K⁴ is isomorphic to
C²(G,A) --δ₂→ C³(G,A) --δ₃→ C⁴(G,A). The three components are the degree-two, degree-three, and
degree-four tuple-coordinate isomorphisms, and they intertwine both differentials. -/
@[simps! hom inv]
def isoShortComplexH3 :
    (inhomogeneousCochains A).sc 3 ≅ shortComplexH3 A :=
  (inhomogeneousCochains A).isoSc' 2 3 4 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₂ A) (cochainsIso₃ A) (cochainsIso₄ A)
      (comp_d₂₃_eq A) (comp_d₃₄_eq A)

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The cycle k-module Z³(K) of the inhomogeneous complex is isomorphic to
Z³(G,A)=ker(δ₃)⊆(G³→A). The isomorphism is induced by the degree-three short-complex coordinate
comparison and leaves the cocycle function unchanged in those coordinates. -/
def isoCocycles₃ : cocycles A 3 ≅ ModuleCat.of k (cocycles₃ A) :=
  cyclesMapIso' (isoShortComplexH3 A) _
    (shortComplexH3 A).moduleCatLeftHomologyData

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The notation H³(G,A) denotes degree-three homology of the nonnegative inhomogeneous cochain
complex. Via its explicit coordinate short complex, it is the k-module ker(δ₃)/im(δ₂) of
three-cocycle classes modulo three-coboundaries. -/
abbrev H3 := groupCohomology A 3

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. The k-linear class map π₃:Z³(G,A)→H³(G,A) first identifies the explicit triple-variable
cocycle with a cycle of the inhomogeneous complex, then takes its cohomology class. It is
surjective, and π₃(z)=0 exactly when z∈im(δ₂). -/
def H3π : ModuleCat.of k (cocycles₃ A) ⟶ H3 A :=
  (isoCocycles₃ A).inv ≫ π A 3

set_option backward.isDefEq.respectTransparency false in
instance : Epi (H3π A) := inferInstanceAs <| Epi (_ ≫ _)

variable {A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem H3π_eq_zero_iff (x : cocycles₃ A) :
    H3π A x = 0 ↔ (x : G × G × G → A) ∈ coboundaries₃ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH3 A).inv
    (shortComplexH3 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 3).leftHomologyIso.hom
  simp only [H3π, isoCocycles₃, π, HomologicalComplex.homologyπ,
    homologyπ, cyclesMapIso'_inv, leftHomologyπ, ← h,
    ← leftHomologyMapIso'_inv, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, map_eq_zero_iff _
      ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₃, shortComplexH3,
    cocycles₃]

theorem H3π_eq_iff (x y : cocycles₃ A) :
    H3π A x = H3π A y ↔
      (x : G × G × G → A) - y ∈ coboundaries₃ A := by
  rw [← sub_eq_zero, ← map_sub, H3π_eq_zero_iff]
  rfl

@[elab_as_elim]
theorem H3_induction_on {C : H3 A → Prop} (x : H3 A)
    (h : ∀ z : cocycles₃ A, C (H3π A z)) : C x :=
  groupCohomology_induction_on x fun y => by
    simpa [H3π] using h ((isoCocycles₃ A).hom y)

end groupCohomology
