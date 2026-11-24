/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexReducedComplex

/-!
# Naturality of raw quotient/kernel Hom-complex normal forms

source and target complex maps induce maps on the raw Hom complex and, under two commuting outer
squares, on its two-sided annihilator subcomplex. The quotient/kernel reconstruction is natural as
an entire complex map and in every integer cohomology degree. Homogeneous cochains need not be
closed.
-/

noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {C A C' A' C'' A'' : CochainComplex D ℤ}

open Cochain

/--
Simultaneous contravariant source and covariant target whiskering of the raw Hom complex by
complex maps.
-/
@[expose]
public def mapOfHom (c : C' ⟶ C) (b : A ⟶ A') :
    CochainComplex.HomComplex C A ⟶ CochainComplex.HomComplex C' A' where
  f n := AddCommGrpCat.ofHom
    { toFun τ :=
        ((Cochain.ofHom c).comp τ (zero_add n)).comp (Cochain.ofHom b) (add_zero n)
      map_zero' := by simp only [Cochain.comp_zero, Cochain.zero_comp]
      map_add' τ σ := by simp only [Cochain.comp_add, Cochain.add_comp] }
  comm' n m _ := by
    apply AddCommGrpCat.ext
    intro τ
    change δ n m
        (((Cochain.ofHom c).comp τ (zero_add n)).comp (Cochain.ofHom b) (add_zero n)) =
      ((Cochain.ofHom c).comp (δ n m τ) (zero_add m)).comp (Cochain.ofHom b) (add_zero m)
    rw [δ_comp_ofHom, δ_ofHom_comp]

/-- Every component is the literal raw pre/post composition. -/
public theorem mapOfHom_f_apply (c : C' ⟶ C) (b : A ⟶ A') (n : ℤ)
    (τ : Cochain C A n) :
    ((mapOfHom c b).f n) τ =
      ((Cochain.ofHom c).comp τ (zero_add n)).comp (Cochain.ofHom b) (add_zero n) :=
  rfl

/-- Identity whiskering is the identity of the entire Hom complex. -/
public theorem mapOfHom_id :
    mapOfHom (𝟙 C) (𝟙 A) = 𝟙 (CochainComplex.HomComplex C A) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro τ
  change ((Cochain.ofHom (𝟙 C)).comp τ (zero_add n)).comp
      (Cochain.ofHom (𝟙 A)) (add_zero n) = τ
  simp only [Cochain.id_comp, Cochain.comp_id]

/-- Source whiskering composes contravariantly, target whiskering covariantly,
as an equality of whole complex maps. -/
public theorem mapOfHom_comp
    (c : C' ⟶ C) (c' : C'' ⟶ C') (b : A ⟶ A') (b' : A' ⟶ A'') :
    mapOfHom c b ≫ mapOfHom c' b' = mapOfHom (c' ≫ c) (b ≫ b') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro τ
  change ((Cochain.ofHom c').comp
      (((Cochain.ofHom c).comp τ (zero_add n)).comp (Cochain.ofHom b) (add_zero n))
      (zero_add n)).comp (Cochain.ofHom b') (add_zero n) =
    ((Cochain.ofHom (c' ≫ c)).comp τ (zero_add n)).comp (Cochain.ofHom (b ≫ b')) (add_zero n)
  apply Cochain.ext
  intro p q hpq
  simp only [comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v,
    HomologicalComplex.comp_f, Category.assoc]

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex.Cochain

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {U C A V U' C' A' V' U'' C'' A'' V'' : CochainComplex D ℤ}

/--
The additive map on the two-sided annihilator induced by the contravariant source square and
covariant target square.
-/
@[expose]
public def annihilatorMap
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') (n : ℤ) :
    annihilator η ε n →+ annihilator η' ε' n where
  toFun τ :=
    ⟨((ofHom c).comp τ.val (zero_add n)).comp (ofHom b) (add_zero n), by
      rw [mem_annihilator]
      have hτ := (mem_annihilator η ε n τ.val).mp τ.property
      constructor
      · apply Cochain.ext
        intro p q hpq
        have hp : η'.f p ≫ c.f p = a.f p ≫ η.f p :=
          congrArg (fun f : U' ⟶ C => f.f p) hpre
        have hv : η.f p ≫ τ.val.v p q hpq = 0 := by
          simpa only [zero_cochain_comp_v, ofHom_v, zero_v] using
            congr_v hτ.1 p q hpq
        simp only [zero_cochain_comp_v, comp_zero_cochain_v, ofHom_v, zero_v]
        calc
          _ = (η'.f p ≫ c.f p) ≫ τ.val.v p q hpq ≫ b.f q := by
            simp only [Category.assoc]
          _ = (a.f p ≫ η.f p) ≫ τ.val.v p q hpq ≫ b.f q := by rw [hp]
          _ = a.f p ≫ ((η.f p ≫ τ.val.v p q hpq) ≫ b.f q) := by
            simp only [Category.assoc]
          _ = 0 := by
            rw [hv, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
      · apply Cochain.ext
        intro p q hpq
        have hp : ε.f q ≫ vmap.f q = b.f q ≫ ε'.f q :=
          congrArg (fun f : A ⟶ V' => f.f q) hpost
        have hv : τ.val.v p q hpq ≫ ε.f q = 0 := by
          simpa only [comp_zero_cochain_v, ofHom_v, zero_v] using
            congr_v hτ.2 p q hpq
        simp only [comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v, zero_v]
        calc
          _ = c.f p ≫ τ.val.v p q hpq ≫ (b.f q ≫ ε'.f q) := by
            simp only [Category.assoc]
          _ = c.f p ≫ τ.val.v p q hpq ≫ (ε.f q ≫ vmap.f q) := by rw [← hp]
          _ = c.f p ≫ ((τ.val.v p q hpq ≫ ε.f q) ≫ vmap.f q) := by
            simp only [Category.assoc]
          _ = 0 := by
            rw [hv, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]⟩
  map_zero' := by
    apply Subtype.ext
    simp only [Cochain.comp_zero, Cochain.zero_comp, ZeroMemClass.coe_zero]
  map_add' τ σ := by
    apply Subtype.ext
    simp only [Cochain.comp_add, Cochain.add_comp, AddSubgroup.coe_add]

/-- The underlying homogeneous cochain is the prescribed literal composite. -/
public theorem annihilatorMap_apply
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') (n : ℤ)
    (τ : annihilator η ε n) :
    (annihilatorMap η ε η' ε' a c b vmap hpre hpost n τ).val =
      ((ofHom c).comp τ.val (zero_add n)).comp (ofHom b) (add_zero n) :=
  rfl

/-- Identity squares induce the identity additive map, in every integer degree. -/
public theorem annihilatorMap_id (η : U ⟶ C) (ε : A ⟶ V) (n : ℤ) :
    annihilatorMap η ε η ε (𝟙 U) (𝟙 C) (𝟙 A) (𝟙 V) (by simp) (by simp) n =
      AddMonoidHom.id (annihilator η ε n) := by
  apply AddMonoidHom.ext
  intro τ
  apply Subtype.ext
  change ((ofHom (𝟙 C)).comp τ.val (zero_add n)).comp (ofHom (𝟙 A)) (add_zero n) =
    τ.val
  simp only [Cochain.id_comp, Cochain.comp_id]

/--
Compatible squares compose on the additive maps. The two composite square proofs are derived here
from the original squares, not extra inputs.
-/
public theorem annihilatorMap_comp
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (η'' : U'' ⟶ C'') (ε'' : A'' ⟶ V'')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (a' : U'' ⟶ U') (c' : C'' ⟶ C') (b' : A' ⟶ A'') (vmap' : V' ⟶ V'')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε')
    (hpre' : η'' ≫ c' = a' ≫ η') (hpost' : ε' ≫ vmap' = b' ≫ ε'') (n : ℤ) :
    let hpreComp : η'' ≫ (c' ≫ c) = (a' ≫ a) ≫ η := by
      calc
        _ = (η'' ≫ c') ≫ c := (Category.assoc η'' c' c).symm
        _ = (a' ≫ η') ≫ c := congrArg (fun f : U'' ⟶ C' => f ≫ c) hpre'
        _ = a' ≫ (η' ≫ c) := Category.assoc a' η' c
        _ = a' ≫ (a ≫ η) := congrArg (fun f : U' ⟶ C => a' ≫ f) hpre
        _ = (a' ≫ a) ≫ η := (Category.assoc a' a η).symm
    let hpostComp : ε ≫ (vmap ≫ vmap') = (b ≫ b') ≫ ε'' := by
      calc
        _ = (ε ≫ vmap) ≫ vmap' := (Category.assoc ε vmap vmap').symm
        _ = (b ≫ ε') ≫ vmap' := congrArg (fun f : A ⟶ V' => f ≫ vmap') hpost
        _ = b ≫ (ε' ≫ vmap') := Category.assoc b ε' vmap'
        _ = b ≫ (b' ≫ ε'') := congrArg (fun f : A' ⟶ V'' => b ≫ f) hpost'
        _ = (b ≫ b') ≫ ε'' := (Category.assoc b b' ε'').symm
    (annihilatorMap η' ε' η'' ε'' a' c' b' vmap' hpre' hpost' n).comp
        (annihilatorMap η ε η' ε' a c b vmap hpre hpost n) =
      annihilatorMap η ε η'' ε'' (a' ≫ a) (c' ≫ c) (b ≫ b') (vmap ≫ vmap')
        hpreComp hpostComp n := by
  dsimp only
  apply AddMonoidHom.ext
  intro τ
  apply Subtype.ext
  change ((ofHom c').comp
      (((ofHom c).comp τ.val (zero_add n)).comp (ofHom b) (add_zero n))
      (zero_add n)).comp (ofHom b') (add_zero n) =
    ((ofHom (c' ≫ c)).comp τ.val (zero_add n)).comp (ofHom (b ≫ b')) (add_zero n)
  apply Cochain.ext
  intro p q hpq
  simp only [comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v,
    HomologicalComplex.comp_f, Category.assoc]

/--
With the four complex maps fixed, changing only proofs of the same two commuting squares does not
change the additive map.
-/
public theorem annihilatorMap_proof_irrel
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre hpre' : η' ≫ c = a ≫ η) (hpost hpost' : ε ≫ vmap = b ≫ ε') (n : ℤ) :
    annihilatorMap η ε η' ε' a c b vmap hpre hpost n =
      annihilatorMap η ε η' ε' a c b vmap hpre' hpost' n := by
  have hp : hpre = hpre' := Subsingleton.elim _ _
  have hv : hpost = hpost' := Subsingleton.elim _ _
  cases hp
  cases hv
  rfl

/--
The annihilator complex map, with the preceding additive maps as its components. Differential
compatibility uses complex maps only.
-/
@[expose]
public def annihilatorComplexMap
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') :
    annihilatorComplex η ε ⟶ annihilatorComplex η' ε' where
  f n := AddCommGrpCat.ofHom (annihilatorMap η ε η' ε' a c b vmap hpre hpost n)
  comm' n m _ := by
    apply AddCommGrpCat.ext
    intro τ
    apply Subtype.ext
    change δ n m
        (((ofHom c).comp τ.val (zero_add n)).comp (ofHom b) (add_zero n)) =
      ((ofHom c).comp (δ n m τ.val) (zero_add m)).comp (ofHom b) (add_zero m)
    rw [δ_comp_ofHom, δ_ofHom_comp]

/-- The degree component is exactly the additive annihilator map. -/
public theorem annihilatorComplexMap_f
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') (n : ℤ) :
    (annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost).f n =
      AddCommGrpCat.ofHom (annihilatorMap η ε η' ε' a c b vmap hpre hpost n) :=
  rfl

/-- The target subgroup is fixed explicitly before exposing its underlying
raw homogeneous cochain. -/
public theorem annihilatorComplexMap_f_apply
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') (n : ℤ)
    (τ : annihilator η ε n) :
    (((annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost).f n) τ :
        annihilator η' ε' n).val =
      ((ofHom c).comp τ.val (zero_add n)).comp (ofHom b) (add_zero n) :=
  rfl

/-- Identity squares give the identity of the entire annihilator complex. -/
public theorem annihilatorComplexMap_id (η : U ⟶ C) (ε : A ⟶ V) :
    annihilatorComplexMap η ε η ε (𝟙 U) (𝟙 C) (𝟙 A) (𝟙 V) (by simp) (by simp) =
      𝟙 (annihilatorComplex η ε) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro τ
  change (annihilatorMap η ε η ε (𝟙 U) (𝟙 C) (𝟙 A) (𝟙 V)
      (by simp) (by simp) n) τ = τ
  exact congrArg (fun f : annihilator η ε n →+ annihilator η ε n => f τ)
    (annihilatorMap_id η ε n)

/-- Compatible squares compose as entire complex maps. Composite square
proofs are derived from the two original source/target squares. -/
public theorem annihilatorComplexMap_comp
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (η'' : U'' ⟶ C'') (ε'' : A'' ⟶ V'')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (a' : U'' ⟶ U') (c' : C'' ⟶ C') (b' : A' ⟶ A'') (vmap' : V' ⟶ V'')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε')
    (hpre' : η'' ≫ c' = a' ≫ η') (hpost' : ε' ≫ vmap' = b' ≫ ε'') :
    let hpreComp : η'' ≫ (c' ≫ c) = (a' ≫ a) ≫ η := by
      calc
        _ = (η'' ≫ c') ≫ c := (Category.assoc η'' c' c).symm
        _ = (a' ≫ η') ≫ c := congrArg (fun f : U'' ⟶ C' => f ≫ c) hpre'
        _ = a' ≫ (η' ≫ c) := Category.assoc a' η' c
        _ = a' ≫ (a ≫ η) := congrArg (fun f : U' ⟶ C => a' ≫ f) hpre
        _ = (a' ≫ a) ≫ η := (Category.assoc a' a η).symm
    let hpostComp : ε ≫ (vmap ≫ vmap') = (b ≫ b') ≫ ε'' := by
      calc
        _ = (ε ≫ vmap) ≫ vmap' := (Category.assoc ε vmap vmap').symm
        _ = (b ≫ ε') ≫ vmap' := congrArg (fun f : A ⟶ V' => f ≫ vmap') hpost
        _ = b ≫ (ε' ≫ vmap') := Category.assoc b ε' vmap'
        _ = b ≫ (b' ≫ ε'') := congrArg (fun f : A' ⟶ V'' => b ≫ f) hpost'
        _ = (b ≫ b') ≫ ε'' := (Category.assoc b b' ε'').symm
    annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost ≫
        annihilatorComplexMap η' ε' η'' ε'' a' c' b' vmap' hpre' hpost' =
      annihilatorComplexMap η ε η'' ε'' (a' ≫ a) (c' ≫ c) (b ≫ b')
        (vmap ≫ vmap') hpreComp hpostComp := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro τ
  have h := annihilatorMap_comp η ε η' ε' η'' ε'' a c b vmap
    a' c' b' vmap' hpre hpost hpre' hpost' n
  dsimp only at h
  exact congrArg (fun f : annihilator η ε n →+ annihilator η'' ε'' n => f τ) h

/-- The whole complex map is independent of proofs of the fixed squares. -/
public theorem annihilatorComplexMap_proof_irrel
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre hpre' : η' ≫ c = a ≫ η) (hpost hpost' : ε ≫ vmap = b ≫ ε') :
    annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost =
      annihilatorComplexMap η ε η' ε' a c b vmap hpre' hpost' := by
  apply HomologicalComplex.hom_ext
  intro n
  change AddCommGrpCat.ofHom (annihilatorMap η ε η' ε' a c b vmap hpre hpost n) =
    AddCommGrpCat.ofHom (annihilatorMap η ε η' ε' a c b vmap hpre' hpost' n)
  exact congrArg (fun f : annihilator η ε n →+ annihilator η' ε' n =>
    AddCommGrpCat.ofHom f)
    (annihilatorMap_proof_irrel η ε η' ε' a c b vmap hpre hpre' hpost hpost' n)

/-- Source-variable and target-variable square transports commute.  -/
public theorem annihilatorComplexMap_source_target_commute
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') :
    annihilatorComplexMap η ε η' ε a c (𝟙 A) (𝟙 V) hpre (by simp) ≫
        annihilatorComplexMap η' ε η' ε' (𝟙 U') (𝟙 C') b vmap (by simp) hpost =
      annihilatorComplexMap η ε η ε' (𝟙 U) (𝟙 C) b vmap (by simp) hpost ≫
        annihilatorComplexMap η ε' η' ε' a c (𝟙 A') (𝟙 V') hpre (by simp) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro τ
  apply Subtype.ext
  change ((ofHom (𝟙 C')).comp
      (((ofHom c).comp τ.val (zero_add n)).comp (ofHom (𝟙 A)) (add_zero n))
      (zero_add n)).comp (ofHom b) (add_zero n) =
    ((ofHom c).comp
      (((ofHom (𝟙 C)).comp τ.val (zero_add n)).comp (ofHom b) (add_zero n))
      (zero_add n)).comp (ofHom (𝟙 A')) (add_zero n)
  simp only [Cochain.id_comp, Cochain.comp_id]
  exact comp_assoc_of_first_is_zero_cochain (ofHom c) τ.val (ofHom b) (add_zero n)

open CategoryTheory.Limits

variable [HasKernels D] [HasCokernels D]

/--
The whole quotient/kernel normal-form isomorphism is natural under the cokernel and kernel maps
induced by the two commuting squares.
-/
public theorem cokernelKernelHomComplexIso_hom_naturality
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    let _ : HasKernel ε' := HomologicalComplex.hasKernel_of_hasKernel_f ε'
    CochainComplex.HomComplex.mapOfHom
        (cokernel.map η' η a c hpre) (kernel.map ε ε' b vmap hpost) ≫
      (cokernelKernelHomComplexIso η' ε').hom =
        (cokernelKernelHomComplexIso η ε).hom ≫
          annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  let _ : HasKernel ε' := HomologicalComplex.hasKernel_of_hasKernel_f ε'
  dsimp only
  let q := cokernel.map η' η a c hpre
  let i := kernel.map ε ε' b vmap hpost
  have hq : cokernel.π η' ≫ q = c ≫ cokernel.π η := cokernel.π_desc _ _ _
  have hi : i ≫ kernel.ι ε' = kernel.ι ε ≫ b := kernel.lift_ι _ _ _
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro θ
  apply Subtype.ext
  change (((cokernelKernelHomComplexIso η' ε').hom.f n)
      (((CochainComplex.HomComplex.mapOfHom q i).f n) θ) :
      annihilator η' ε' n).val =
    (((annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost).f n)
      (((cokernelKernelHomComplexIso η ε).hom.f n) θ : annihilator η ε n) :
      annihilator η' ε' n).val
  let θAnn : annihilator η ε n :=
    ((cokernelKernelHomComplexIso η ε).hom.f n) θ
  let θMapped : Cochain (cokernel η') (kernel ε') n :=
    ((CochainComplex.HomComplex.mapOfHom q i).f n) θ
  let θRaw : Cochain C A n :=
    ((ofHom (cokernel.π η)).comp θ (zero_add n)).comp
      (ofHom (kernel.ι ε)) (add_zero n)
  have hθAnn : θAnn.val = θRaw :=
    cokernelKernelHomComplexIso_hom_f_apply η ε n θ
  have hθMapped : θMapped =
      ((ofHom q).comp θ (zero_add n)).comp (ofHom i) (add_zero n) :=
    CochainComplex.HomComplex.mapOfHom_f_apply q i n θ
  have hLeft :
      (((cokernelKernelHomComplexIso η' ε').hom.f n) θMapped :
        annihilator η' ε' n).val =
      ((ofHom (cokernel.π η')).comp
        (((ofHom q).comp θ (zero_add n)).comp (ofHom i) (add_zero n))
        (zero_add n)).comp (ofHom (kernel.ι ε')) (add_zero n) :=
    (cokernelKernelHomComplexIso_hom_f_apply η' ε' n θMapped).trans
      (congrArg (fun z : Cochain (cokernel η') (kernel ε') n =>
        ((ofHom (cokernel.π η')).comp z (zero_add n)).comp
          (ofHom (kernel.ι ε')) (add_zero n)) hθMapped)
  have hRight :
      (((annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost).f n) θAnn :
        annihilator η' ε' n).val =
      ((ofHom c).comp θRaw (zero_add n)).comp (ofHom b) (add_zero n) :=
    (annihilatorComplexMap_f_apply η ε η' ε' a c b vmap hpre hpost n θAnn).trans
      (congrArg (fun z : Cochain C A n =>
        ((ofHom c).comp z (zero_add n)).comp (ofHom b) (add_zero n)) hθAnn)
  have hRaw :
      ((ofHom (cokernel.π η')).comp
        (((ofHom q).comp θ (zero_add n)).comp (ofHom i) (add_zero n))
        (zero_add n)).comp (ofHom (kernel.ι ε')) (add_zero n) =
      ((ofHom c).comp θRaw (zero_add n)).comp (ofHom b) (add_zero n) := by
    apply Cochain.ext
    intro p r hpr
    have hqp : (cokernel.π η').f p ≫ q.f p = c.f p ≫ (cokernel.π η).f p :=
      congrArg (fun f : C' ⟶ cokernel η => f.f p) hq
    have hir : i.f r ≫ (kernel.ι ε').f r = (kernel.ι ε).f r ≫ b.f r :=
      congrArg (fun f : kernel ε ⟶ A' => f.f r) hi
    simp only [θRaw, comp_zero_cochain_v, zero_cochain_comp_v, ofHom_v]
    calc
      _ = ((cokernel.π η').f p ≫ q.f p) ≫ θ.v p r hpr ≫
          (i.f r ≫ (kernel.ι ε').f r) := by simp only [Category.assoc]
      _ = (c.f p ≫ (cokernel.π η).f p) ≫ θ.v p r hpr ≫
          ((kernel.ι ε).f r ≫ b.f r) := by rw [hqp, hir]
      _ = _ := by simp only [Category.assoc]
  exact hLeft.trans (hRaw.trans hRight.symm)

/--
The inverse normal-form square follows from the complex isomorphisms; the induced q/i maps need
not be invertible.
-/
public theorem cokernelKernelHomComplexIso_inv_naturality
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    let _ : HasKernel ε' := HomologicalComplex.hasKernel_of_hasKernel_f ε'
    (cokernelKernelHomComplexIso η ε).inv ≫
        CochainComplex.HomComplex.mapOfHom
          (cokernel.map η' η a c hpre) (kernel.map ε ε' b vmap hpost) =
      annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost ≫
        (cokernelKernelHomComplexIso η' ε').inv := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  let _ : HasKernel ε' := HomologicalComplex.hasKernel_of_hasKernel_f ε'
  dsimp only
  let e := cokernelKernelHomComplexIso η ε
  let e' := cokernelKernelHomComplexIso η' ε'
  let T := CochainComplex.HomComplex.mapOfHom
    (cokernel.map η' η a c hpre) (kernel.map ε ε' b vmap hpost)
  let F := annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost
  have h : T ≫ e'.hom = e.hom ≫ F :=
    cokernelKernelHomComplexIso_hom_naturality η ε η' ε' a c b vmap hpre hpost
  apply (cancel_mono e'.hom).1
  calc
    (e.inv ≫ T) ≫ e'.hom = e.inv ≫ (T ≫ e'.hom) := Category.assoc e.inv T e'.hom
    _ = e.inv ≫ (e.hom ≫ F) := congrArg (fun f => e.inv ≫ f) h
    _ = (e.inv ≫ e.hom) ≫ F := (Category.assoc e.inv e.hom F).symm
    _ = F := by rw [e.inv_hom_id, Category.id_comp]
    _ = (F ≫ e'.inv) ≫ e'.hom := by
      rw [Category.assoc, e'.inv_hom_id, Category.comp_id]

/--
Applying the abelian-group homology functor gives naturality of the existing normal-form
cohomology isomorphism in every integer degree.
-/
public theorem cokernelKernelCohomologyIso_hom_naturality
    (η : U ⟶ C) (ε : A ⟶ V) (η' : U' ⟶ C') (ε' : A' ⟶ V')
    (a : U' ⟶ U) (c : C' ⟶ C) (b : A ⟶ A') (vmap : V ⟶ V')
    (hpre : η' ≫ c = a ≫ η) (hpost : ε ≫ vmap = b ≫ ε') (n : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
    let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
    let _ : HasKernel ε' := HomologicalComplex.hasKernel_of_hasKernel_f ε'
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n
    H.map (CochainComplex.HomComplex.mapOfHom
        (cokernel.map η' η a c hpre) (kernel.map ε ε' b vmap hpost)) ≫
      (cokernelKernelCohomologyIso η' ε' n).hom =
        (cokernelKernelCohomologyIso η ε n).hom ≫
          H.map (annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
  let _ : HasKernel ε := HomologicalComplex.hasKernel_of_hasKernel_f ε
  let _ : HasKernel ε' := HomologicalComplex.hasKernel_of_hasKernel_f ε'
  dsimp only
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n
  change H.map (CochainComplex.HomComplex.mapOfHom
      (cokernel.map η' η a c hpre) (kernel.map ε ε' b vmap hpost)) ≫
      H.map (cokernelKernelHomComplexIso η' ε').hom =
    H.map (cokernelKernelHomComplexIso η ε).hom ≫
      H.map (annihilatorComplexMap η ε η' ε' a c b vmap hpre hpost)
  exact (H.map_comp _ _).symm.trans
    ((congrArg H.map
      (cokernelKernelHomComplexIso_hom_naturality η ε η' ε' a c b vmap hpre hpost)).trans
      (H.map_comp _ _))

end CochainComplex.HomComplex.Cochain
