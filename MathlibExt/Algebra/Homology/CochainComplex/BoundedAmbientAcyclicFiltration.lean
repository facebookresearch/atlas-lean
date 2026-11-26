/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTruncationAt

/-!
# Finite filtration by upper kernel truncations

Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and F:E → A an additive fully faithful exact functor to
an abelian category. Assume F reflects admissible exactness and its
essential image is closed under kernels of epimorphisms between image objects.

For K supported in [a,b] with F(K) acyclic, successive upper kernel
truncations give stages K_n supported in [a,b−n], all ambient acyclic.
Their inclusions are degreewise admissible monomorphisms.
Projection onto the signed top disk has positive upper identity and lower
differential components. The corresponding mapped rows are short exact,
and their cofiber descendants become quasi-isomorphisms under F.

The process starts at K and terminates in a zero complex after
L=(b−a+1).toNat steps. The support endpoints are carried throughout the
construction, and category object/morphism universes remain independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CochainComplex.Bounded.TruncationFiltration

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic.

The stage structure records S, its explicit term-support interval [a,b−n] and acyclicity of F(S). -/
structure Stage (a b : ℤ) (n : ℕ) where
  /-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic.

The bounded complex S at the specified truncation stage. -/
  complex : Bounded E
  /-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic.

The support condition says S^j=0 for j<a or b−n<j. -/
  support : ∀ j : ℤ, j < a ∨ b - (n : ℤ) < j → IsZero (complex.obj.X j)
  /-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic.

The image complex F(S) is acyclic in the ambient abelian category. -/
  acyclic : ((F.mapHomologicalComplex (.up ℤ)).obj complex.obj).Acyclic

variable [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

namespace Stage

variable {F} {a b : ℤ} {n : ℕ}

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t.

The next stage is S′, with support [a,b−n−1] and ambient acyclicity. -/
def next (S : Stage F a b n) : Stage F a b (n + 1) where
  complex := TruncationAt.topTruncation (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic
  support := by
    intro j hj
    apply TruncationAt.topTruncationRaw_support (b := b - (n : ℤ)) (a := a)
      (hSupport := S.support) F hKernelClosure S.complex S.acyclic j
    omega
  acyclic := TruncationAt.topTruncation_map_acyclic (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t.

The complex object of the next stage is precisely the upper kernel truncation at the carried endpoint t=b−n. -/
theorem next_complex (S : Stage F a b n) :
    (next hKernelClosure S).complex =
      TruncationAt.topTruncation (b := b - (n : ℤ)) (a := a)
        (hSupport := S.support) F hKernelClosure S.complex S.acyclic := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t.

The bounded cochain inclusion i:S′ → S from the next stage to the current stage. -/
def inclusion (S : Stage F a b n) : (next hKernelClosure S).complex ⟶ S.complex :=
  TruncationAt.topTruncationι (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

Every degree component of i is an admissible monomorphism in E. -/
theorem inclusion_isAdmissibleMono_f (S : Stage F a b n) (j : ℤ) :
    IsAdmissibleMono ((inclusion hKernelClosure S).hom.f j) :=
  TruncationAt.topTruncationι_isAdmissibleMono_f (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic j

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E has a zero object and binary biproducts, and put t=b−n.

The signed top disk D_t is formed from the top term S^t in degrees t−1 and t. -/
abbrev disk (S : Stage F a b n) : Bounded E :=
  TruncationAt.topDisk (b := b - (n : ℤ)) S.complex

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E has a zero object and binary biproducts, and put t=b−n.

The cochain projection π:S → D_t to the signed disk of the top term. -/
abbrev projection (S : Stage F a b n) : S.complex ⟶ disk S :=
  TruncationAt.topDiskProjectionBounded (b := b - (n : ℤ)) S.complex

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E has a zero object and binary biproducts, and put t=b−n.

In the upper disk coordinate S^t → D_t^t, the projection component π_t is the canonical upper comparison map. -/
theorem projection_f_upper (S : Stage F a b n) :
    (projection S).hom.f (b - (n : ℤ)) =
      (TruncationAt.topDiskUpperIso (b := b - (n : ℤ)) S.complex).hom :=
  TruncationAt.topDiskProjection_f_upper (b := b - (n : ℤ)) S.complex

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E has a zero object and binary biproducts, and put t=b−n.

The lower projection component π_{t−1} is d_S^{t−1} followed by the canonical lower disk coordinate S^t → D_t^{t−1}, with positive sign. -/
theorem projection_f_lower (S : Stage F a b n) :
    (projection S).hom.f (b - (n : ℤ) - 1) =
      S.complex.obj.d (b - (n : ℤ) - 1) (b - (n : ℤ)) ≫
        (TruncationAt.topDiskLowerIso (b := b - (n : ℤ)) S.complex).hom :=
  TruncationAt.topDiskProjection_f_lower (b := b - (n : ℤ)) S.complex

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The composite π∘i is zero as a bounded cochain map. -/
theorem inclusion_projection (S : Stage F a b n) :
    inclusion hKernelClosure S ≫ projection S = 0 :=
  TruncationAt.topTruncationι_projection (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The underlying cochain short complex is S′ —i→ S —π→ D_t. -/
abbrev rawRow (S : Stage F a b n) : ShortComplex (CochainComplex E ℤ) :=
  TruncationAt.topTruncationRawShortComplex (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The first map of the underlying stage short complex is the cochain inclusion i. -/
theorem rawRow_f (S : Stage F a b n) :
    (rawRow hKernelClosure S).f = (inclusion hKernelClosure S).hom := rfl

omit [F.IsExact] in
/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The second map of the underlying stage short complex is the cochain projection π. -/
theorem rawRow_g (S : Stage F a b n) :
    (rawRow hKernelClosure S).g = (projection S).hom := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

Applying F termwise to S′ → S → D_t gives a short exact sequence of ambient cochain complexes. -/
theorem rawRow_map_shortExact (S : Stage F a b n) :
    ((rawRow hKernelClosure S).map (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  TruncationAt.topTruncationRawShortComplex_map_shortExact (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The stage cofiber is the bounded homotopy cofiber Cofib(i). -/
abbrev cofiber (S : Stage F a b n) : Bounded E :=
  TruncationAt.topTruncationCofiber (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The cofiber descendant Cofib(i) → D_t is induced by π and the zero composite π∘i. -/
abbrev descendant (S : Stage F a b n) : cofiber hKernelClosure S ⟶ disk S :=
  TruncationAt.topTruncationCofiberDesc (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The underlying complex of the stage cofiber is the homotopy cofiber of the underlying inclusion i. -/
theorem cofiber_obj (S : Stage F a b n) :
    (cofiber hKernelClosure S).obj =
      HomologicalComplex.homotopyCofiber (inclusion hKernelClosure S).hom := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The cofiber target inclusion S → Cofib(i) followed by the descendant equals π. -/
theorem descendant_inr (S : Stage F a b n) :
    HomologicalComplex.homotopyCofiber.inr (inclusion hKernelClosure S).hom ≫
      (descendant hKernelClosure S).hom = (projection S).hom :=
  TruncationAt.topTruncationCofiber_inr_desc (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

Every shifted-source component of the descendant Cofib(i) → D_t is zero, as prescribed by its zero homotopy. -/
theorem descendant_inlX_f (S : Stage F a b n) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    HomologicalComplex.homotopyCofiber.inlX (inclusion hKernelClosure S).hom j i hij ≫
      (descendant hKernelClosure S).hom.f i = 0 :=
  TruncationAt.topTruncationCofiber_inlX_desc_f (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic i j hij

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The canonical additive-functor comparison F(Cofib(i)) ≅ Cofib(F(i)) for the stage inclusion. -/
abbrev cofiberMapIso (S : Stage F a b n) :
    (F.mapHomologicalComplex (.up ℤ)).obj (cofiber hKernelClosure S).obj ≅
      HomologicalComplex.homotopyCofiber
        ((F.mapHomologicalComplex (.up ℤ)).map (inclusion hKernelClosure S).hom) :=
  TruncationAt.topTruncationCofiberMapIso (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

Under F(Cofib(i)) ≅ Cofib(F(i)), the image of the stage descendant is the canonical descendant of the mapped short exact row. -/
theorem descendant_map (S : Stage F a b n) :
    (cofiberMapIso hKernelClosure S).hom ≫
      HomologicalComplex.homotopyCofiber.descShortComplex
        ((rawRow hKernelClosure S).map (F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map (descendant hKernelClosure S).hom :=
  TruncationAt.topTruncationCofiberDesc_map (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
A stage S with indices a,b∈ℤ and n∈ℕ is a bounded complex
supported in [a,b−n] whose ambient image F(S) is acyclic. Assume E is Quillen exact with a zero object and binary biproducts,
F is fully faithful, exact and reflects admissible exactness, and its
essential image is closed under kernels of epimorphisms between image objects.
Put t=b−n and S′ for the upper kernel truncation of S at t. Write i:S′ → S for its inclusion, D_t for the signed top disk,
and π:S → D_t for the projection.

The image under F of the stage descendant Cofib(i) → D_t is a quasi-isomorphism. -/
theorem descendant_map_quasiIso (S : Stage F a b n) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (descendant hKernelClosure S).hom) :=
  TruncationAt.topTruncationCofiberDesc_map_quasiIso (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

end Stage

variable (K : Bounded E) (a b : ℤ)
variable (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
variable (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic.

The recursive stage K_n is obtained by n successive upper kernel truncations, retaining support [a,b−n] and ambient acyclicity. -/
def stage : (n : ℕ) → Stage F a b n :=
  Nat.rec
    { complex := K
      support := by simpa only [Nat.cast_zero, sub_zero] using hSupport
      acyclic := hK }
    (fun _ S => S.next hKernelClosure)

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic.

The initial complex of the truncation filtration is K_0=K. -/
theorem stage_zero_complex : (stage F hKernelClosure K a b hSupport hK 0).complex = K := rfl

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic.

The complete stage at n+1 is the next-stage construction applied to the stage at n. -/
theorem stage_succ (n : ℕ) :
    stage F hKernelClosure K a b hSupport hK (n + 1) =
      (stage F hKernelClosure K a b hSupport hK n).next hKernelClosure := rfl

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic.

The n-th filtration arrow is the bounded inclusion K_{n+1} → K_n. -/
def inclusion (n : ℕ) :
    (stage F hKernelClosure K a b hSupport hK (n + 1)).complex ⟶
      (stage F hKernelClosure K a b hSupport hK n).complex :=
  (stage F hKernelClosure K a b hSupport hK n).inclusion hKernelClosure

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic.

Each stage K_n has zero terms for j<a or b−n<j. -/
theorem stage_support (n : ℕ) :
    ∀ j : ℤ, j < a ∨ b - (n : ℤ) < j →
      IsZero ((stage F hKernelClosure K a b hSupport hK n).complex.obj.X j) :=
  (stage F hKernelClosure K a b hSupport hK n).support

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic.

Every ambient image F(K_n) is acyclic. -/
theorem stage_map_acyclic (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (stage F hKernelClosure K a b hSupport hK n).complex.obj).Acyclic :=
  (stage F hKernelClosure K a b hSupport hK n).acyclic

omit F hKernelClosure K hSupport hK in
/-- For integers a,b, consider the finite term interval [a,b].

The number of truncation steps is L=(b−a+1).toNat, the nonnegative interval length. -/
def length : ℕ := (b - a + 1).toNat

omit F hKernelClosure K hSupport hK in
/-- For a,b∈ℤ, put L=(b−a+1).toNat.

The terminal upper bound satisfies b−L<a. -/
theorem terminal_upper_lt : b - (length a b : ℤ) < a := by
  dsimp only [length]
  omega

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic. Put L=(b−a+1).toNat.

The underlying cochain complex of K_L is zero, since its support [a,b−L] is empty. -/
theorem terminal_raw_isZero :
    IsZero ((stage F hKernelClosure K a b hSupport hK (length a b)).complex.obj) :=
  TruncationAt.isZero_of_empty_window (b := b - (length a b : ℤ))
    (stage F hKernelClosure K a b hSupport hK (length a b)).complex a
    (stage_support F hKernelClosure K a b hSupport hK (length a b)) (terminal_upper_lt a b)

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive, fully faithful, exact and
reflecting admissible exactness. Assume its essential image is closed under
kernels of epimorphisms between image objects.
Let K be supported in [a,b] and F(K) acyclic. Put L=(b−a+1).toNat.

The terminal stage K_L is a zero object of the bounded cochain category. -/
theorem terminal_isZero :
    IsZero ((stage F hKernelClosure K a b hSupport hK (length a b)).complex) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (fullyFaithfulι E).map_injective
  exact (IsZero.iff_id_eq_zero _).mp (terminal_raw_isZero F hKernelClosure K a b hSupport hK)

end CochainComplex.Bounded.TruncationFiltration

end
