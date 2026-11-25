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
# Finite filtration by the original ambient-acyclic truncations

The original bounded cochain and explicit support window are retained.
Each step is the same actual kernel truncation at the explicit upper bound.
Its support and ambient acyclicity are carried through ordinary `Nat.rec`.
The inclusions, source and mapped rows, signed disks and cofiber descendants
are precisely the original constructors of `TruncationAt`.

After the object-local length of the original support interval, the actual
terminal complex is zero. No intermediate upper bound is chosen from a
bounded predicate. All four object and Hom universes remain independent.
No source homology, global kernels, uniform bound or comparison outcome is
assumed. This filtration does not assert the same-E Gillet–Waldhausen theorem.
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

/-- Stage data records the original bounded object and its earned explicit support and acyclicity. -/
structure Stage (a b : ℤ) (n : ℕ) where
  /-- The actual original bounded cochain at this stage. -/
  complex : Bounded E
  /-- The original lower endpoint and the explicit decreased upper endpoint. -/
  support : ∀ j : ℤ, j < a ∨ b - (n : ℤ) < j → IsZero (complex.obj.X j)
  /-- Acyclicity in the same specified ambient raw complex category. -/
  acyclic : ((F.mapHomologicalComplex (.up ℤ)).obj complex.obj).Acyclic

variable [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

namespace Stage

variable {F} {a b : ℤ} {n : ℕ}

/-- The next stage is the same actual truncation at the explicitly carried upper endpoint. -/
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

/-- The entire next stage object is precisely the stock original kernel truncation. -/
theorem next_complex (S : Stage F a b n) :
    (next hKernelClosure S).complex =
      TruncationAt.topTruncation (b := b - (n : ℤ)) (a := a)
        (hSupport := S.support) F hKernelClosure S.complex S.acyclic := rfl

/-- The original bounded inclusion from the next stage to the current stage. -/
def inclusion (S : Stage F a b n) : (next hKernelClosure S).complex ⟶ S.complex :=
  TruncationAt.topTruncationι (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Every actual inclusion component is admissible in the original exact source. -/
theorem inclusion_isAdmissibleMono_f (S : Stage F a b n) (j : ℤ) :
    IsAdmissibleMono ((inclusion hKernelClosure S).hom.f j) :=
  TruncationAt.topTruncationι_isAdmissibleMono_f (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic j

/-- The original disk at the explicitly carried upper endpoint. -/
abbrev disk (S : Stage F a b n) : Bounded E :=
  TruncationAt.topDisk (b := b - (n : ℤ)) S.complex

/-- The same entire current-complex projection onto its actual signed top disk. -/
abbrev projection (S : Stage F a b n) : S.complex ⟶ disk S :=
  TruncationAt.topDiskProjectionBounded (b := b - (n : ℤ)) S.complex

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- The actual upper projection component retains the original positive identity chart. -/
theorem projection_f_upper (S : Stage F a b n) :
    (projection S).hom.f (b - (n : ℤ)) =
      (TruncationAt.topDiskUpperIso (b := b - (n : ℤ)) S.complex).hom :=
  TruncationAt.topDiskProjection_f_upper (b := b - (n : ℤ)) S.complex

omit [ExactCategory E] [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact] [F.IsExact] in
/-- The actual lower component uses the same original differential with its positive sign. -/
theorem projection_f_lower (S : Stage F a b n) :
    (projection S).hom.f (b - (n : ℤ) - 1) =
      S.complex.obj.d (b - (n : ℤ) - 1) (b - (n : ℤ)) ≫
        (TruncationAt.topDiskLowerIso (b := b - (n : ℤ)) S.complex).hom :=
  TruncationAt.topDiskProjection_f_lower (b := b - (n : ℤ)) S.complex

/-- The whole original inclusion/projection face remains zero at every stage. -/
theorem inclusion_projection (S : Stage F a b n) :
    inclusion hKernelClosure S ≫ projection S = 0 :=
  TruncationAt.topTruncationι_projection (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- The complete actual raw kernel/projection row for this original stage. -/
abbrev rawRow (S : Stage F a b n) : ShortComplex (CochainComplex E ℤ) :=
  TruncationAt.topTruncationRawShortComplex (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- The complete first row map is the same original raw inclusion. -/
theorem rawRow_f (S : Stage F a b n) :
    (rawRow hKernelClosure S).f = (inclusion hKernelClosure S).hom := rfl

omit [F.IsExact] in
/-- The complete second row map is the same original raw disk projection. -/
theorem rawRow_g (S : Stage F a b n) :
    (rawRow hKernelClosure S).g = (projection S).hom := rfl

/-- The specified exact embedding maps the same whole original row to a short exact row. -/
theorem rawRow_map_shortExact (S : Stage F a b n) :
    ((rawRow hKernelClosure S).map (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  TruncationAt.topTruncationRawShortComplex_map_shortExact (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- The same actual signed cofiber of the inclusion at this original stage. -/
abbrev cofiber (S : Stage F a b n) : Bounded E :=
  TruncationAt.topTruncationCofiber (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- The original cofiber descendant to the actual signed disk at this stage. -/
abbrev descendant (S : Stage F a b n) : cofiber hKernelClosure S ⟶ disk S :=
  TruncationAt.topTruncationCofiberDesc (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- The entire actual stage cofiber is the original signed cofiber of its whole raw inclusion. -/
theorem cofiber_obj (S : Stage F a b n) :
    (cofiber hKernelClosure S).obj =
      HomologicalComplex.homotopyCofiber (inclusion hKernelClosure S).hom := rfl

/-- The whole old-complex face of the original descendant is the same original projection. -/
theorem descendant_inr (S : Stage F a b n) :
    HomologicalComplex.homotopyCofiber.inr (inclusion hKernelClosure S).hom ≫
      (descendant hKernelClosure S).hom = (projection S).hom :=
  TruncationAt.topTruncationCofiber_inr_desc (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Every original shifted-source component face is the same actual zero homotopy. -/
theorem descendant_inlX_f (S : Stage F a b n) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    HomologicalComplex.homotopyCofiber.inlX (inclusion hKernelClosure S).hom j i hij ≫
      (descendant hKernelClosure S).hom.f i = 0 :=
  TruncationAt.topTruncationCofiber_inlX_desc_f (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic i j hij

/-- The actual whole ambient cofiber comparison is the same original additive-functor chart. -/
abbrev cofiberMapIso (S : Stage F a b n) :
    (F.mapHomologicalComplex (.up ℤ)).obj (cofiber hKernelClosure S).obj ≅
      HomologicalComplex.homotopyCofiber
        ((F.mapHomologicalComplex (.up ℤ)).map (inclusion hKernelClosure S).hom) :=
  TruncationAt.topTruncationCofiberMapIso (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- Both original faces retain the whole mapped descendant through the actual cofiber chart. -/
theorem descendant_map (S : Stage F a b n) :
    (cofiberMapIso hKernelClosure S).hom ≫
      HomologicalComplex.homotopyCofiber.descShortComplex
        ((rawRow hKernelClosure S).map (F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map (descendant hKernelClosure S).hom :=
  TruncationAt.topTruncationCofiberDesc_map (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

/-- The complete original descendant is a weak equivalence through the actual ambient functor. -/
theorem descendant_map_quasiIso (S : Stage F a b n) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (descendant hKernelClosure S).hom) :=
  TruncationAt.topTruncationCofiberDesc_map_quasiIso (b := b - (n : ℤ)) (a := a)
    (hSupport := S.support) F hKernelClosure S.complex S.acyclic

end Stage

variable (K : Bounded E) (a b : ℤ)
variable (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
variable (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)

/-- Iterate the same actual truncation constructors with the original explicit window. -/
def stage : (n : ℕ) → Stage F a b n :=
  Nat.rec
    { complex := K
      support := by simpa only [Nat.cast_zero, sub_zero] using hSupport
      acyclic := hK }
    (fun _ S => S.next hKernelClosure)

/-- The entire initial bounded object is the unchanged original cochain. -/
theorem stage_zero_complex : (stage F hKernelClosure K a b hSupport hK 0).complex = K := rfl

/-- Each whole next object is obtained by the same original stage constructor. -/
theorem stage_succ (n : ℕ) :
    stage F hKernelClosure K a b hSupport hK (n + 1) =
      (stage F hKernelClosure K a b hSupport hK n).next hKernelClosure := rfl

/-- The actual original inclusion from one filtration stage to the preceding stage. -/
def inclusion (n : ℕ) :
    (stage F hKernelClosure K a b hSupport hK (n + 1)).complex ⟶
      (stage F hKernelClosure K a b hSupport hK n).complex :=
  (stage F hKernelClosure K a b hSupport hK n).inclusion hKernelClosure

/-- All original terms retain the explicitly carried original interval at every stage. -/
theorem stage_support (n : ℕ) :
    ∀ j : ℤ, j < a ∨ b - (n : ℤ) < j →
      IsZero ((stage F hKernelClosure K a b hSupport hK n).complex.obj.X j) :=
  (stage F hKernelClosure K a b hSupport hK n).support

/-- Every original filtration object remains acyclic through the same ambient functor. -/
theorem stage_map_acyclic (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj
      (stage F hKernelClosure K a b hSupport hK n).complex.obj).Acyclic :=
  (stage F hKernelClosure K a b hSupport hK n).acyclic

omit F hKernelClosure K hSupport hK in
/-- The number of steps is the local length of the original geometric support interval. -/
def length : ℕ := (b - a + 1).toNat

omit F hKernelClosure K hSupport hK in
/-- The explicit upper endpoint lies below the original lower endpoint after this many steps. -/
theorem terminal_upper_lt : b - (length a b : ℤ) < a := by
  dsimp only [length]
  omega

/-- The same actual terminal raw complex is zero by its explicitly carried empty window. -/
theorem terminal_raw_isZero :
    IsZero ((stage F hKernelClosure K a b hSupport hK (length a b)).complex.obj) :=
  TruncationAt.isZero_of_empty_window (b := b - (length a b : ℤ))
    (stage F hKernelClosure K a b hSupport hK (length a b)).complex a
    (stage_support F hKernelClosure K a b hSupport hK (length a b)) (terminal_upper_lt a b)

/-- The unchanged actual terminal object is also zero in the original bounded category. -/
theorem terminal_isZero :
    IsZero ((stage F hKernelClosure K a b hSupport hK (length a b)).complex) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (fullyFaithfulι E).map_injective
  exact (IsZero.iff_id_eq_zero _).mp (terminal_raw_isZero F hKernelClosure K a b hSupport hK)

end CochainComplex.Bounded.TruncationFiltration

end
