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

public import MathlibExt.Algebra.Homology.SpectralObject.AbutmentFiltration
public import MathlibExt.Algebra.Homology.SpectralObject.FiniteStripConvergence
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialMittagLefflerLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.SpectralObject.EpiMono
/-!
# Stable images and restriction-kernel graded quotients

For a sequential inverse tower G of abelian groups and compatible maps
γ:G → const(M), the kernel of the restriction from a limiting cone point
to M is the limit of the stage kernels Ker(γ_k).
If that kernel tower is Mittag–Leffler, its projection image at stage zero
equals every sufficiently late transition image. Finite stage groups
supply the Mittag–Leffler condition.

For an abelian-group spectral object S on a preorder with endpoints,
take an antitone sequence a_k of left cuts and a₀≤c.
The right-interval tower is G_k=H_Sⁿ(a_k,⊤), with restrictions to
H_Sⁿ(c,⊤) and full-endpoint cone point A=H_Sⁿ(⊥,⊤).
If this cone is limiting and the kernel image is attained at R, the
window E_Sⁿ(a_R,a₀,c,⊤) is canonically the graded quotient F_c/F_{a₀},
where F_i=Ker(A → H_Sⁿ(i,⊤)).
A finite right endpoint d≥c gives the same comparison when
H_S^{n−1}(d,⊤)=0. This yields the skeletal page comparison with cuts
a_k=−p−1−k. The group-carrier and cut-index universes are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows Opposite
open scoped ZeroObject

universe u v

namespace CategoryTheory.Limits

variable {G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}} {M : AddCommGrpCat.{u}}

/-- For N∈ℕ, consider the opposite order category ℕᵒᵖ.

The tail-index functor sends stage k to N+k and sends a transition to the corresponding transition between shifted stages. -/
abbrev stableImageTailIndex (N : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ where
  obj j := op (N + j.unop)
  map f := (homOfLE (Nat.add_le_add_left (leOfHom f.unop) N)).op

/-- Let G be a sequential inverse tower of abelian groups and N∈ℕ.

The natural map from the shifted tower (G_{N+k})_k to G has stage-k component G_{N+k} → G_k. -/
def stableImageTailProjection (G : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (N : ℕ) :
    stableImageTailIndex N ⋙ G ⟶ G where
  app j := G.map (homOfLE (show j.unop ≤ N + j.unop by omega)).op
  naturality i j f := by
    change G.map ((stableImageTailIndex N).map f) ≫
        G.map (homOfLE (show j.unop ≤ N + j.unop by omega)).op =
      G.map (homOfLE (show i.unop ≤ N + i.unop by omega)).op ≫ G.map f
    rw [← G.map_comp, ← G.map_comp] <;> congr 1 <;> subsingleton

/-- Let G be a sequential inverse tower of abelian groups and c a cone with coordinates π_k:A → G_k.

For N∈ℕ, the restricted tail cone has the same point A and coordinates π_{N+k}:A → G_{N+k}. -/
abbrev stableImageTailCone (c : Cone G) (N : ℕ) : Cone (stableImageTailIndex N ⋙ G) :=
  c.whisker (stableImageTailIndex N)

/-- Let G be an inverse tower of abelian groups and d a cone on its tail (G_{N+k})_k.

The extended cone on G has the same point and stage-k coordinate d_k followed by G_{N+k} → G_k. -/
abbrev stableImageTailConeExtend (N : ℕ) (d : Cone (stableImageTailIndex N ⋙ G)) : Cone G :=
  ⟨d.pt, d.π ≫ stableImageTailProjection G N⟩

/-- Let G be an inverse tower of abelian groups and c a limiting cone over G.

For every N∈ℕ, restriction to the stages N+k is a limiting cone over the tail tower, retaining the original coordinates at those stages. -/
def stableImageTailConeIsLimit (c : Cone G) (hc : IsLimit c) (N : ℕ) :
    IsLimit (stableImageTailCone c N) where
  lift d := hc.lift (stableImageTailConeExtend N d)
  fac d j := by
    change hc.lift (stableImageTailConeExtend N d) ≫ c.π.app (op (N + j.unop)) = d.π.app j
    rw [hc.fac]
    exact d.w ((homOfLE (show j.unop ≤ N + j.unop by omega)).op)
  uniq d m hm := by
    apply hc.hom_ext
    intro j
    let f : op (N + j.unop) ⟶ j := (homOfLE (show j.unop ≤ N + j.unop by omega)).op
    calc
      m ≫ c.π.app j = m ≫ c.π.app (op (N + j.unop)) ≫ G.map f := by rw [c.w f]
      _ = d.π.app j ≫ G.map f := by
        have hj : m ≫ c.π.app (op (N + j.unop)) = d.π.app j := hm j
        rw [← Category.assoc, hj]
      _ = hc.lift (stableImageTailConeExtend N d) ≫ c.π.app j := by rw [hc.fac]; rfl

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k).

The inverse kernel tower has stage k equal to K_k and transitions induced by those of G through the compatible restriction kernels. -/
def stableImageKernelTower (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj j := kernel (γ.app j)
  map {i j} f := kernel.map (γ.app i) (γ.app j) (G.map f) (𝟙 M)
    (by simpa using (γ.naturality f).symm)
  map_id j := by
    apply (cancel_mono (kernel.ι (γ.app j))).mp
    simp
  map_comp {i j k} f g := by
    apply (cancel_mono (kernel.ι (γ.app k))).mp
    simp [G.map_comp, Category.assoc]

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k).

The stage inclusions K_k↪G_k form a natural transformation K → G. -/
def stableImageKernelInclusion (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) :
    stableImageKernelTower γ ⟶ G where
  app j := kernel.ι (γ.app j)
  naturality i j f := by
    exact kernel.lift_ι _ _ _

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M.

The restriction ρ:A → M is π₀ followed by γ₀; by compatibility it equals γ_k∘π_k at every stage k. -/
def stableImageConeRestriction (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) : c.pt ⟶ M :=
  c.π.app (op 0) ≫ γ.app (op 0)

theorem stableImageCone_lower_eq (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (j : ℕᵒᵖ) : c.π.app j ≫ γ.app j = stableImageConeRestriction γ c := by
  let f : j ⟶ op 0 := (homOfLE (Nat.zero_le j.unop)).op
  have hγ : G.map f ≫ γ.app (op 0) = γ.app j := by simpa using γ.naturality f
  rw [← hγ, ← Category.assoc, c.w f]
  rfl

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M.

The kernel Ker(ρ) carries a cone over the kernel tower K. Its coordinate into K_k is induced by π_k and the inclusion Ker(ρ)↪A. -/
def stableImageKernelCone (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) :
    Cone (stableImageKernelTower γ) where
  pt := kernel (stableImageConeRestriction γ c)
  π :=
    { app := fun j => kernel.lift (γ.app j)
        (kernel.ι (stableImageConeRestriction γ c) ≫ c.π.app j) (by
          rw [Category.assoc, stableImageCone_lower_eq]
          exact kernel.condition _)
      naturality := by
        intro i j f
        apply (cancel_mono (kernel.ι (γ.app j))).mp
        simp only [Functor.const_obj_map, Category.id_comp, Category.assoc,
          stableImageKernelTower, kernel.map, kernel.lift_ι_assoc, kernel.lift_ι]
        rw [c.w f]
        simp }

@[reassoc]
theorem stableImageKernelCone_π_ι (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (j : ℕᵒᵖ) :
    (stableImageKernelCone γ c).π.app j ≫ kernel.ι (γ.app j) =
      kernel.ι (stableImageConeRestriction γ c) ≫ c.π.app j :=
  kernel.lift_ι _ _ _

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k).

A cone d over K gives a cone over G by composing each coordinate d.pt → K_k with K_k↪G_k. -/
def stableImageKernelConeForget (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (d : Cone (stableImageKernelTower γ)) : Cone G :=
  ⟨d.pt, d.π ≫ stableImageKernelInclusion γ⟩

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M. Assume c is limiting.

For any cone d over K, the unique lift of its underlying G-cone to A factors through Ker(ρ), giving a map d.pt → Ker(ρ). -/
def stableImageKernelConeLift (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (d : Cone (stableImageKernelTower γ)) :
    d.pt ⟶ (stableImageKernelCone γ c).pt :=
  kernel.lift (stableImageConeRestriction γ c)
    (hc.lift (stableImageKernelConeForget γ d)) (by
      unfold stableImageConeRestriction
      rw [← Category.assoc, hc.fac]
      change (d.π.app (op 0) ≫ kernel.ι (γ.app (op 0))) ≫ γ.app (op 0) = 0
      simp only [Category.assoc, kernel.condition, comp_zero])

@[reassoc]
theorem stableImageKernelConeLift_ι (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (d : Cone (stableImageKernelTower γ)) :
    stableImageKernelConeLift γ c hc d ≫ kernel.ι (stableImageConeRestriction γ c) =
      hc.lift (stableImageKernelConeForget γ d) :=
  kernel.lift_ι _ _ _

theorem stableImageKernelConeLift_fac (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (d : Cone (stableImageKernelTower γ)) (j : ℕᵒᵖ) :
    stableImageKernelConeLift γ c hc d ≫ (stableImageKernelCone γ c).π.app j = d.π.app j := by
  apply (cancel_mono (kernel.ι (γ.app j))).mp
  rw [Category.assoc, stableImageKernelCone_π_ι, ← Category.assoc,
    stableImageKernelConeLift_ι, hc.fac]
  rfl

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M. Assume c is limiting.

The induced cone with point Ker(ρ) is limiting for the stage-kernel tower K. -/
def stableImageKernelConeIsLimit (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) : IsLimit (stableImageKernelCone γ c) where
  lift := stableImageKernelConeLift γ c hc
  fac := stableImageKernelConeLift_fac γ c hc
  uniq d m hm := by
    apply (cancel_mono (kernel.ι (stableImageConeRestriction γ c))).mp
    apply hc.hom_ext
    intro j
    calc
      (m ≫ kernel.ι (stableImageConeRestriction γ c)) ≫ c.π.app j =
        m ≫ (stableImageKernelCone γ c).π.app j ≫ kernel.ι (γ.app j) := by
          rw [Category.assoc, ← stableImageKernelCone_π_ι, ← Category.assoc]
      _ = d.π.app j ≫ kernel.ι (γ.app j) := by rw [← Category.assoc, hm]
      _ = (stableImageKernelConeLift γ c hc d ≫ kernel.ι (stableImageConeRestriction γ c)) ≫
          c.π.app j := by
        rw [stableImageKernelConeLift_ι, hc.fac]
        rfl

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M. Assume c is limiting.

The canonical isomorphism Ker(ρ) ≅ lim K compares the induced kernel cone with the chosen inverse limit of the kernel tower. -/
def stableImageKernelLimitIso (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) :
    kernel (stableImageConeRestriction γ c) ≅ limit (stableImageKernelTower γ) :=
  (stableImageKernelConeIsLimit γ c hc).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc]
theorem stableImageKernelLimitIso_hom_π (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (c : Cone G) (hc : IsLimit c) (j : ℕᵒᵖ) :
    (stableImageKernelLimitIso γ c hc).hom ≫ limit.π (stableImageKernelTower γ) j =
      (stableImageKernelCone γ c).π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M.

The evaluation edge Ker(ρ) → G₀ is the inclusion into A followed by the stage-zero cone coordinate π₀. -/
def stableImageKernelConeEdge (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) :
    kernel (stableImageConeRestriction γ c) ⟶ G.obj (op 0) :=
  kernel.ι (stableImageConeRestriction γ c) ≫ c.π.app (op 0)

theorem stableImageRange_comp_of_epi {A B D : AddCommGrpCat.{u}}
    (e : A ⟶ B) [Epi e] (f : B ⟶ D) : Set.range (e ≫ f) = Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective e).mp inferInstance x
    exact ⟨z, rfl⟩

theorem stableImageRange_postcomp_eq {A B D Q : AddCommGrpCat.{u}}
    (f : A ⟶ D) (g : B ⟶ D) (t : D ⟶ Q) (h : Set.range f = Set.range g) :
    Set.range (f ≫ t) = Set.range (g ≫ t) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ : f x ∈ Set.range g := h ▸ Set.mem_range_self x
    refine ⟨z, ?_⟩
    exact congrArg t hz
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ : g x ∈ Set.range f := h.symm ▸ Set.mem_range_self x
    refine ⟨z, ?_⟩
    exact congrArg t hz

theorem stableImageKernelEdge_range_congr {A M Q : AddCommGrpCat.{u}}
    (f g : A ⟶ M) (t : A ⟶ Q) (h : f = g) :
    Set.range (kernel.ι f ≫ t) = Set.range (kernel.ι g ≫ t) := by
  cases h
  rfl

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Let c be a cone over G with point A and coordinates π_k.
Set ρ=γ₀∘π₀:A → M. Assume c is limiting and K is Mittag–Leffler.

If the eventual image in K₀ is attained by K_R → K₀, then the image of Ker(ρ) → G₀ equals the image of K_R → K₀ ↪ G₀. -/
theorem stableImageKernelConeEdge_range
    (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M) (c : Cone G) (hc : IsLimit c)
    (hML : (stableImageKernelTower γ).IsSequentialMittagLeffler) (R : ℕ)
    (hR : ((stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op)) :
    Set.range (stableImageKernelConeEdge γ c) =
      Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op ≫
        kernel.ι (γ.app (op 0))) := by
  have hπ : Set.range (limit.π (stableImageKernelTower γ) (op 0)) =
      Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op) :=
    (Concrete.range_limit_π_eq_eventualRange_of_isMittagLeffler _ hML 0).trans hR
  have hfac : (stableImageKernelLimitIso γ c hc).hom ≫
      (limit.π (stableImageKernelTower γ) (op 0) ≫ kernel.ι (γ.app (op 0))) =
        stableImageKernelConeEdge γ c := by
    rw [← Category.assoc, stableImageKernelLimitIso_hom_π, stableImageKernelCone_π_ι]
    rfl
  rw [← hfac, stableImageRange_comp_of_epi]
  exact stableImageRange_postcomp_eq _ _ _ hπ

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k). Assume K is Mittag–Leffler.

There exists N such that for every R≥N, the eventual image in K₀ equals the image of K_R → K₀. -/
theorem stableImageKernelTower_attainedRange
    (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (hML : (stableImageKernelTower γ).IsSequentialMittagLeffler) :
    ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
      ((stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
        Set.range ((stableImageKernelTower γ).map (homOfLE (Nat.zero_le R)).op) := by
  let U := (stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}
  obtain ⟨j, f, hf⟩ := U.isMittagLeffler_iff_eventualRange.mp hML (op 0)
  refine ⟨j.unop, fun R hR => ?_⟩
  change U.eventualRange (op 0) = Set.range (U.map (homOfLE (Nat.zero_le R)).op)
  have h := U.eventualRange_eq_range_precomp ((homOfLE hR).op) f hf
  have he : (homOfLE hR).op ≫ f = (homOfLE (Nat.zero_le R)).op := Subsingleton.elim _ _
  simpa only [he] using h

/-- Let G be a sequential inverse tower of abelian groups, M an abelian
group, and γ:G → const(M) a compatible family of restriction maps.
Write K_k=Ker(γ_k).

If every group G_k has a finite underlying set, then the kernel tower K is Mittag–Leffler. -/
theorem stableImageKernelTower_isMittagLeffler_of_finite
    (γ : G ⟶ (Functor.const ℕᵒᵖ).obj M)
    (hFinite : ∀ j : ℕᵒᵖ, _root_.Finite (G.obj j)) :
    (stableImageKernelTower γ).IsSequentialMittagLeffler := by
  let U := (stableImageKernelTower γ) ⋙ forget AddCommGrpCat.{u}
  apply U.isMittagLeffler_of_exists_finite_range
  intro j
  letI : _root_.Finite (G.obj j) := hFinite j
  letI : _root_.Finite ((stableImageKernelTower γ).obj j) :=
    _root_.Finite.of_injective (kernel.ι (γ.app j))
      ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
  letI : _root_.Finite (U.obj j) := by
    change _root_.Finite (kernel (γ.app j) : AddCommGrpCat.{u})
    exact _root_.Finite.of_injective (kernel.ι (γ.app j))
      ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
  exact ⟨j, 𝟙 _, Set.toFinite _⟩

end CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

variable {ι : Type v} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (S : SpectralObject AddCommGrpCat.{u} ι)

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

The right-interval group B_i=H_Sⁿ(i,⊤). -/
def stableImageRightObject (n : ℤ) (i : ι) : AddCommGrpCat.{u} :=
  (S.H n).obj (mk₁ (stableIntervalRight i))

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i≤j, the restriction B_i → B_j induced by the inclusion of the upper interval j≤⊤ into i≤⊤. -/
def stableImageRightMap (n : ℤ) {i j : ι} (hij : i ≤ j) :
    stableImageRightObject S n i ⟶ stableImageRightObject S n j :=
  (S.H n).map (twoδ₁Toδ₀ (homOfLE hij) (stableIntervalRight j)
    (stableIntervalRight i) (by subsingleton))

-- Keep the original bounded-order parameter in this compatibility declaration.
@[simp, nolint unusedArguments]
theorem stableImageRightMap_id (n : ℤ) (i : ι) :
    stableImageRightMap S n (le_refl i) = 𝟙 (stableImageRightObject S n i) := by
  dsimp only [stableImageRightMap]
  have h : twoδ₁Toδ₀ (homOfLE (le_refl i)) (stableIntervalRight i)
      (stableIntervalRight i) (by subsingleton) = 𝟙 (mk₁ (stableIntervalRight i)) := Subsingleton.elim _ _
  rw [h, (S.H n).map_id]
  rfl

-- Keep the original bounded-order parameter in this compatibility declaration.
@[reassoc, nolint unusedArguments]
theorem stableImageRightMap_comp (n : ℤ) {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    stableImageRightMap S n hij ≫ stableImageRightMap S n hjk =
      stableImageRightMap S n (hij.trans hjk) := by
  dsimp only [stableImageRightMap]
  rw [← (S.H n).map_comp] <;> congr 1 <;> subsingleton

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₁≤i₂, the top-endpoint page window W=E_Sⁿ(i₀≤i₁≤i₂≤⊤). -/
def stableImagePageWindow (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    AddCommGrpCat.{u} :=
  S.E (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂) (n - 1) n (n + 1)

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₁≤i₂, the canonical inclusion E_Sⁿ(i₀,i₁,i₂,⊤) → B_{i₁} of the page-window image into the right-interval group. -/
def stableImagePageWindowToRight (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    stableImagePageWindow S n h₀₁ h₁₂ ⟶ stableImageRightObject S n i₁ :=
  S.ιE (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂) (n - 1) n (n + 1) ≫
    S.fromOpcycles (homOfLE h₁₂) (stableIntervalRight i₂) (stableIntervalRight i₁) (by subsingleton) n

instance stableImagePageWindowToRight_mono (n : ℤ) {i₀ i₁ i₂ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) : Mono (stableImagePageWindowToRight S n h₀₁ h₁₂) := by
  dsimp only [stableImagePageWindowToRight]
  infer_instance

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₁≤i₂, the canonical map from relative classes H_Sⁿ(i₀,i₂) onto E_Sⁿ(i₀,i₁,i₂,⊤). -/
def stableImagePageWindowFromRelative (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    (S.H n).obj (mk₁ (homOfLE (h₀₁.trans h₁₂))) ⟶ stableImagePageWindow S n h₀₁ h₁₂ :=
  S.toCycles (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE (h₀₁.trans h₁₂)) (by subsingleton) n ≫
    S.πE (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂) (n - 1) n (n + 1)

instance stableImagePageWindowFromRelative_epi (n : ℤ) {i₀ i₁ i₂ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) : Epi (stableImagePageWindowFromRelative S n h₀₁ h₁₂) := by
  dsimp only [stableImagePageWindowFromRelative]
  infer_instance

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₂, the exact short complex H_Sⁿ(i₀,i₂) → B_{i₀} → B_{i₂} from the interval triple i₀≤i₂≤⊤. -/
def stableImageIntervalKernelSequence (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    ShortComplex AddCommGrpCat.{u} :=
  S.sc₂ (homOfLE h₀₂) (stableIntervalRight i₂) (stableIntervalRight i₀) (by subsingleton) n

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₂, the map H_Sⁿ(i₀,i₂) → Ker(B_{i₀} → B_{i₂}) induced by interval exactness; it covers the restriction kernel. -/
def stableImageIntervalKernelLift (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    (S.H n).obj (mk₁ (homOfLE h₀₂)) ⟶ kernel (stableImageRightMap S n h₀₂) :=
  (stableImageIntervalKernelSequence S n h₀₂).toCycles ≫
    (stableImageIntervalKernelSequence S n h₀₂).cyclesIsoKernel.hom

instance stableImageIntervalKernelLift_epi (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    Epi (stableImageIntervalKernelLift S n h₀₂) := by
  letI : Epi (stableImageIntervalKernelSequence S n h₀₂).toCycles :=
    (S.exact₂ (homOfLE h₀₂) (stableIntervalRight i₂) (stableIntervalRight i₀) (by subsingleton) n).epi_toCycles
  dsimp only [stableImageIntervalKernelLift]
  infer_instance

-- Keep the original bounded-order parameter in this compatibility declaration.
@[reassoc, nolint unusedArguments]
theorem stableImageIntervalKernelLift_ι (n : ℤ) {i₀ i₂ : ι} (h₀₂ : i₀ ≤ i₂) :
    stableImageIntervalKernelLift S n h₀₂ ≫ kernel.ι (stableImageRightMap S n h₀₂) =
      (stableImageIntervalKernelSequence S n h₀₂).f := by
  dsimp only [stableImageIntervalKernelLift]
  change (stableImageIntervalKernelSequence S n h₀₂).toCycles ≫
      (stableImageIntervalKernelSequence S n h₀₂).cyclesIsoKernel.hom ≫
        kernel.ι (stableImageIntervalKernelSequence S n h₀₂).g = _
  simp only [Category.assoc, ShortComplex.cyclesIsoKernel, kernel.lift_ι, ShortComplex.toCycles_i]

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₁≤i₂, relative classes mapped through E_Sⁿ(i₀,i₁,i₂,⊤) into B_{i₁} give the same map as their lift to Ker(B_{i₀} → B_{i₂}), followed by its inclusion into B_{i₀} and restriction to B_{i₁}. -/
theorem stableImagePageWindowFromRelative_comp_right
    (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    stableImagePageWindowFromRelative S n h₀₁ h₁₂ ≫ stableImagePageWindowToRight S n h₀₁ h₁₂ =
      stableImageIntervalKernelLift S n (h₀₁.trans h₁₂) ≫
        (kernel.ι (stableImageRightMap S n (h₀₁.trans h₁₂)) ≫ stableImageRightMap S n h₀₁) := by
  have hπ := S.πE_ιE (homOfLE h₀₁) (homOfLE h₁₂) (stableIntervalRight i₂)
    (n - 1) n (n + 1) (by omega) (by omega)
  have hπ' := congrArg (fun t => t ≫
    S.fromOpcycles (homOfLE h₁₂) (stableIntervalRight i₂) (stableIntervalRight i₁)
      (by subsingleton) n) hπ
  simp only [Category.assoc] at hπ'
  dsimp only [stableImagePageWindowFromRelative, stableImagePageWindowToRight]
  simp only [Category.assoc]
  rw [hπ', S.toCycles_i_assoc, S.p_fromOpcycles, stableImageIntervalKernelLift_ι_assoc]
  change (S.H n).map (twoδ₁Toδ₀ (homOfLE h₀₁) (homOfLE h₁₂)
      (homOfLE (h₀₁.trans h₁₂)) (by subsingleton)) ≫
      (S.H n).map (twoδ₂Toδ₁ (homOfLE h₁₂) (stableIntervalRight i₂)
        (stableIntervalRight i₁) (by subsingleton)) =
    (S.H n).map (twoδ₂Toδ₁ (homOfLE (h₀₁.trans h₁₂)) (stableIntervalRight i₂)
      (stableIntervalRight i₀) (by subsingleton)) ≫ stableImageRightMap S n h₀₁
  dsimp only [stableImageRightMap]
  rw [← (S.H n).map_comp, ← (S.H n).map_comp] <;> congr 1 <;> subsingleton

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₀≤i₁≤i₂, the image of E_Sⁿ(i₀,i₁,i₂,⊤) → B_{i₁} equals the image of Ker(B_{i₀} → B_{i₂}) → B_{i₀} → B_{i₁}. -/
theorem stableImagePageWindowToRight_range
    (n : ℤ) {i₀ i₁ i₂ : ι} (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) :
    Set.range (stableImagePageWindowToRight S n h₀₁ h₁₂) =
      Set.range (kernel.ι (stableImageRightMap S n (h₀₁.trans h₁₂)) ≫ stableImageRightMap S n h₀₁) := by
  rw [← stableImageRange_comp_of_epi (stableImagePageWindowFromRelative S n h₀₁ h₁₂),
    stableImagePageWindowFromRelative_comp_right, stableImageRange_comp_of_epi]

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For an antitone sequence a:ℕ → ι, the inverse right-interval tower has stage k equal to B_{a_k}, with restriction transitions induced by a_m≤a_k for k≤m. -/
def stableImageRightTower (n : ℤ) (a : ℕ → ι) (ha : Antitone a) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj j := stableImageRightObject S n (a j.unop)
  map f := stableImageRightMap S n (ha (leOfHom f.unop))
  map_id j := stableImageRightMap_id S n (a j.unop)
  map_comp f g := (stableImageRightMap_comp S n _ _).symm

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k.

The compatible restrictions G_k=B_{a_k} → B_c form the natural transformation γ:G → const(B_c). -/
def stableImageTowerRestriction (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) :
    stableImageRightTower S n a ha ⟶ (Functor.const ℕᵒᵖ).obj (stableImageRightObject S n c) where
  app j := stableImageRightMap S n ((ha (Nat.zero_le j.unop)).trans hc)
  naturality i j f := by
    change stableImageRightMap S n (ha (leOfHom f.unop)) ≫
        stableImageRightMap S n ((ha (Nat.zero_le j.unop)).trans hc) =
      stableImageRightMap S n ((ha (Nat.zero_le i.unop)).trans hc) ≫ 𝟙 _
    rw [stableImageRightMap_comp, Category.comp_id]

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For an antitone sequence a:ℕ → ι, the natural cone over the right-interval tower has point A=H_Sⁿ(⊥,⊤) and stage-k coordinate A → B_{a_k}. -/
def stableImageTotalCone (n : ℤ) (a : ℕ → ι) (ha : Antitone a) :
    Cone (stableImageRightTower S n a ha) where
  pt := stableImageRightObject S n (⊥ : ι)
  π :=
    { app := fun j => stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a j.unop)
      naturality := by
        intro i j f
        change 𝟙 _ ≫ stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a j.unop) =
          stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a i.unop) ≫
            stableImageRightMap S n (ha (leOfHom f.unop))
        rw [Category.id_comp, stableImageRightMap_comp] }

theorem stableImageTotalCone_restriction (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) :
    stableImageConeRestriction (stableImageTowerRestriction S n a ha c hc)
        (stableImageTotalCone S n a ha) =
      stableImageRightMap S n (bot_le : (⊥ : ι) ≤ c) :=
  stableImageRightMap_comp S n _ _

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k.

For R∈ℕ, the stable-to-finite map E_Sⁿ(⊥,a₀,c,⊤) → E_Sⁿ(a_R,a₀,c,⊤) changes only the left endpoint by the canonical window-indexing map. -/
def stableImagePageComparison (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    stableImagePageWindow S n (bot_le : (⊥ : ι) ≤ a 0) hc ⟶
      stableImagePageWindow S n (ha (Nat.zero_le R)) hc :=
  S.map (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c)
    (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c)
    (homMk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a R)) (𝟙 (a 0)) (𝟙 c) (𝟙 (⊤ : ι))
      (by subsingleton) (by subsingleton) (by subsingleton))
    (n - 1) n (n + 1) (by omega) (by omega)

@[reassoc]
theorem stableImagePageComparison_comp_right (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    stableImagePageComparison S n a ha c hc R ≫
        stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc =
      stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc := by
  let α : mk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c) ⟶
      mk₃ (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c) :=
    homMk₃ (homOfLE (bot_le : (⊥ : ι) ≤ a R)) (𝟙 (a 0)) (𝟙 c) (𝟙 (⊤ : ι))
      (by subsingleton) (by subsingleton) (by subsingleton)
  have hmap := S.map_ιE (homOfLE (bot_le : (⊥ : ι) ≤ a 0)) (homOfLE hc) (stableIntervalRight c)
    (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (stableIntervalRight c) α
    (𝟙 (mk₂ (homOfLE hc) (stableIntervalRight c))) (n - 1) n (n + 1)
    (by subsingleton) (by omega) (by omega)
  simp only [S.opcyclesMap_id, Category.comp_id] at hmap
  simpa only [α, stableImagePageComparison, stableImagePageWindow, stableImagePageWindowToRight,
    stableImageRightObject, Category.assoc] using
    congrArg (fun t => t ≫ S.fromOpcycles (homOfLE hc) (stableIntervalRight c)
      (stableIntervalRight (a 0)) (by subsingleton) n) hmap

instance stableImagePageComparison_mono (n : ℤ) (a : ℕ → ι) (ha : Antitone a)
    (c : ι) (hc : a 0 ≤ c) (R : ℕ) : Mono (stableImagePageComparison S n a ha c hc R) :=
  mono_of_mono_fac (stableImagePageComparison_comp_right S n a ha c hc R)

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k.

The image of E_Sⁿ(⊥,a₀,c,⊤) → B_{a₀} equals the image of the total restriction kernel F_c → A → B_{a₀}. -/
theorem stableImageStableWindow_range
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c) :
    Set.range (stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc) =
      Set.range (stableImageKernelConeEdge (stableImageTowerRestriction S n a ha c hc)
        (stableImageTotalCone S n a ha)) := by
  rw [stableImagePageWindowToRight_range]
  have h := stableImageKernelEdge_range_congr
    (stableImageConeRestriction (stableImageTowerRestriction S n a ha c hc) (stableImageTotalCone S n a ha))
    (stableImageRightMap S n (bot_le : (⊥ : ι) ≤ c))
    (stableImageRightMap S n (bot_le : (⊥ : ι) ≤ a 0))
    (stableImageTotalCone_restriction S n a ha c hc)
  exact h.symm

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k.

For R∈ℕ, the image of E_Sⁿ(a_R,a₀,c,⊤) → B_{a₀} equals the image of K_R → K₀ ↪ B_{a₀}. -/
theorem stableImageFiniteWindow_range
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c) (R : ℕ) :
    Set.range (stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
          (homOfLE (Nat.zero_le R)).op ≫
        kernel.ι ((stableImageTowerRestriction S n a ha c hc).app (op 0))) := by
  rw [stableImagePageWindowToRight_range]
  have h := (stableImageKernelInclusion (stableImageTowerRestriction S n a ha c hc)).naturality
    ((homOfLE (Nat.zero_le R)).op)
  exact (congrArg (fun f :
    (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).obj (op R) ⟶
      stableImageRightObject S n (a 0) => Set.range f) h).symm

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k. Assume this full-endpoint cone is limiting and K is
Mittag–Leffler. Fix R∈ℕ at which the image of K_R → K₀ equals the
eventual image in K₀.

The canonical stable-to-finite window map E_Sⁿ(⊥,a₀,c,⊤) → E_Sⁿ(a_R,a₀,c,⊤) is an isomorphism. -/
theorem stableImagePageComparison_isIso
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    IsIso (stableImagePageComparison S n a ha c hc R) := by
  have hRange : Set.range (stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc) =
      Set.range (stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc) :=
    (stableImageStableWindow_range S n a ha c hc).trans
      ((stableImageKernelConeEdge_range _ _ hTotal hML R hR).trans
        (stableImageFiniteWindow_range S n a ha c hc R).symm)
  have hSurj : Function.Surjective (stableImagePageComparison S n a ha c hc R) := by
    intro y
    obtain ⟨x, hx⟩ : stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc y ∈
        Set.range (stableImagePageWindowToRight S n (bot_le : (⊥ : ι) ≤ a 0) hc) :=
      hRange.symm ▸ Set.mem_range_self y
    refine ⟨x, ?_⟩
    apply ((AddCommGrpCat.mono_iff_injective (stableImagePageWindowToRight S n
      (ha (Nat.zero_le R)) hc)).mp inferInstance)
    change (stableImagePageComparison S n a ha c hc R ≫
      stableImagePageWindowToRight S n (ha (Nat.zero_le R)) hc) x = _
    rw [stableImagePageComparison_comp_right]
    exact hx
  letI : Epi (stableImagePageComparison S n a ha c hc R) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hSurj
  exact isIso_of_mono_of_epi _

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k. Assume the full-endpoint cone is limiting and every G_k has a finite underlying set.

There is N such that for every R≥N, the canonical stable-to-finite window map E_Sⁿ(⊥,a₀,c,⊤) → E_Sⁿ(a_R,a₀,c,⊤) is an isomorphism. -/
theorem stableImagePageComparison_eventually_isIso_of_finite
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hFinite : ∀ j : ℕᵒᵖ, _root_.Finite ((stableImageRightTower S n a ha).obj j)) :
    ∃ N : ℕ, ∀ R : ℕ, N ≤ R → IsIso (stableImagePageComparison S n a ha c hc R) := by
  have hML := stableImageKernelTower_isMittagLeffler_of_finite
    (stableImageTowerRestriction S n a ha c hc) hFinite
  obtain ⟨N, hN⟩ := stableImageKernelTower_attainedRange (stableImageTowerRestriction S n a ha c hc) hML
  exact ⟨N, fun R hR => stableImagePageComparison_isIso S n a ha c hc hTotal hML R (hN R hR)⟩

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k. Assume this full-endpoint cone is limiting and K is
Mittag–Leffler. Fix R∈ℕ at which the image of K_R → K₀ equals the
eventual image in K₀.

The canonical isomorphism E_Sⁿ(a_R,a₀,c,⊤) ≅ F_c/F_{a₀}, obtained from the inverse stable-to-finite map and the endpoint kernel-graded comparison. -/
def stableImageKernelGradedIso
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    stableImagePageWindow S n (ha (Nat.zero_le R)) hc ≅ S.stableIntervalKernelGraded n hc := by
  letI := stableImagePageComparison_isIso S n a ha c hc hTotal hML R hR
  exact (asIso (stableImagePageComparison S n a ha c hc R)).symm ≪≫ S.stableIntervalKernelGradedIso n hc

@[reassoc]
theorem stableImageKernelGradedIso_comparison
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op)) :
    stableImagePageComparison S n a ha c hc R ≫
        (stableImageKernelGradedIso S n a ha c hc hTotal hML R hR).hom =
      (S.stableIntervalKernelGradedIso n hc).hom := by
  letI := stableImagePageComparison_isIso S n a ha c hc hTotal hML R hR
  simp only [stableImageKernelGradedIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i). Let a:ℕ → ι be antitone and a₀≤c.
Set G_k=B_{a_k}, γ_k:G_k → B_c, K_k=Ker(γ_k), and let the full-endpoint
cone have point A and coordinates A → G_k. Assume this full-endpoint cone is limiting and K is
Mittag–Leffler. Fix R∈ℕ at which the image of K_R → K₀ equals the
eventual image in K₀. Let d≥c and assume H_S^{n−1}(d,⊤)=0.

The canonical comparison E_Sⁿ(a_R,a₀,c,d) ≅ F_c/F_{a₀}, padding only its right endpoint before the stable-image comparison. -/
def stableImageFiniteWindowKernelGradedIso
    (n : ℤ) (a : ℕ → ι) (ha : Antitone a) (c : ι) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (d : ι) (hcd : c ≤ d)
    (hRight : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d)))) :
    S.E (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
        (n - 1) n (n + 1) (by omega) (by omega) ≅ S.stableIntervalKernelGraded n hc :=
  S.isoMapFourδ₄Toδ₃' (a R) (a 0) c d (⊤ : ι)
    (ha (Nat.zero_le R)) hc hcd le_top (n - 1) n (n + 1) hRight (by omega) (by omega) ≪≫
      stableImageKernelGradedIso S n a ha c hc hTotal hML R hR

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For ordered cut chains i₀≤i₁≤i₂≤i₃ and j₀≤j₁≤j₂≤j₃ with iₐ=jₐ for all four cuts, the canonical identification E_Sⁿ(i₀,i₁,i₂,i₃) ≅ E_Sⁿ(j₀,j₁,j₂,j₃). -/
def stableImageWindowEqIso (n : ℤ) {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (h₀₁' : j₀ ≤ j₁) (h₁₂' : j₁ ≤ j₂) (h₂₃' : j₂ ≤ j₃)
    (e₀ : i₀ = j₀) (e₁ : i₁ = j₁) (e₂ : i₂ = j₂) (e₃ : i₃ = j₃) :
    S.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃) (n - 1) n (n + 1) ≅
      S.E (homOfLE h₀₁') (homOfLE h₁₂') (homOfLE h₂₃') (n - 1) n (n + 1) := by
  subst j₀ j₁ j₂ j₃
  exact Iso.refl _

/-- Let ι be a preorder with endpoints and S an abelian-group spectral
object indexed by ι. In degree n∈ℤ put B_i=H_Sⁿ(i,⊤),
A=H_Sⁿ(⊥,⊤) and F_i=Ker(A → B_i).

For i₁≤i₂ and j₁≤j₂ with i₁=j₁ and i₂=j₂, the canonical identification F_{i₂}/F_{i₁} ≅ F_{j₂}/F_{j₁}. -/
def stableImageKernelGradedEqIso (n : ℤ) {i₁ i₂ j₁ j₂ : ι}
    (h : i₁ ≤ i₂) (h' : j₁ ≤ j₂) (e₁ : i₁ = j₁) (e₂ : i₂ = j₂) :
    S.stableIntervalKernelGraded n h ≅ S.stableIntervalKernelGraded n h' := by
  subst j₁ j₂
  exact Iso.refl _

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject

variable (S : SpectralObject AddCommGrpCat.{u} EInt)

/-- For a column p∈ℤ and k∈ℕ, regard integer cuts as elements of EInt.

The skeletal left-cut sequence is a_k=−(p+1)−k, an antitone sequence whose k-th cut is the left endpoint of page k+1. -/
def stableImageSkeletalLeftCuts (p : ℤ) (k : ℕ) : EInt := ((-(p + 1) - (k : ℤ) : ℤ) : EInt)

theorem stableImageSkeletalLeftCuts_antitone (p : ℤ) : Antitone (stableImageSkeletalLeftCuts p) := by
  intro i j hij
  simp [stableImageSkeletalLeftCuts]
  omega

theorem stableImageSkeletal_middle (p : ℤ) : stableImageSkeletalLeftCuts p 0 ≤ ((-p : ℤ) : EInt) := by
  simp [stableImageSkeletalLeftCuts]

/-- Let S be an EInt-indexed abelian-group spectral object, p,q∈ℤ and n=p+q.
Put a_k=−p−1−k, c=−p, G_k=H_Sⁿ(a_k,+∞) and
K_k=Ker(G_k → H_Sⁿ(c,+∞)). Assume the full-endpoint cone
H_Sⁿ(−∞,+∞) → G is limiting and K is Mittag–Leffler.
Let R attain the eventual image in K₀ and assume
H_S^{n−1}(−p+R,+∞)=0.

The canonical page comparison E_{R+1}^{p,q} ≅ FᵖA_n/Fᵖ⁺¹A_n, where A_n=H_Sⁿ(−∞,+∞) and FᵖA_n=Ker(A_n → H_Sⁿ(−p,+∞)). -/
def stableImageSkeletalPageGradedIso (p q : ℤ)
    (hTotal : IsLimit (stableImageTotalCone S (p + q) (stableImageSkeletalLeftCuts p)
      (stableImageSkeletalLeftCuts_antitone p)))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S (p + q)
      (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
      ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙ forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map (homOfLE (Nat.zero_le R)).op))
    (hRight : IsZero ((S.H (p + q - 1)).obj
      (mk₁ (stableIntervalRight (((-p + (R : ℤ) : ℤ) : EInt)))))) :
    ((S.skeletalSpectralSequence).page ((R : ℤ) + 1) (by omega)).X (p, q) ≅
      S.skeletalAbutmentGraded (p + q) p := by
  let r : ℤ := (R : ℤ) + 1
  let a := stableImageSkeletalLeftCuts p
  let ha := stableImageSkeletalLeftCuts_antitone p
  let c : EInt := ((-p : ℤ) : EInt)
  let hc := stableImageSkeletal_middle p
  let d : EInt := ((-p + (R : ℤ) : ℤ) : EInt)
  have hcd : c ≤ d := by simp [c, d]
  let he : S.E
      (homOfLE (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; dsimp [r]; omega))
      (homOfLE (show ((-(p + 1) : ℤ) : EInt) ≤ c by simp [c]))
      (homOfLE (show c ≤ ((-p + r - 1 : ℤ) : EInt) by simp [c]; dsimp [r]; omega))
      (p + q - 1) (p + q) (p + q + 1) ≅
      S.E (homOfLE (ha (Nat.zero_le R))) (homOfLE hc) (homOfLE hcd)
        (p + q - 1) (p + q) (p + q + 1) :=
    stableImageWindowEqIso S (p + q) _ _ _ _ _ _
      (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [a, stableImageSkeletalLeftCuts, r]; omega)
      (by simp [a, stableImageSkeletalLeftCuts]) rfl
      (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [d, r]; omega)
  let egrade : S.stableIntervalKernelGraded (p + q) hc ≅ S.skeletalAbutmentGraded (p + q) p :=
    stableImageKernelGradedEqIso S (p + q) hc
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (by simp [a, stableImageSkeletalLeftCuts]) rfl
  exact S.skeletalPageWindowIso r (by dsimp [r]; omega) p q ≪≫ he ≪≫
    stableImageFiniteWindowKernelGradedIso S (p + q) a ha c hc hTotal hML R hR
      d hcd hRight ≪≫ egrade

end CategoryTheory.Abelian.SpectralObject


end
