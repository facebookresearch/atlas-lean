/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel

/-!
# Product-ring idempotents and module decomposition

For rings `R` and `S`, the elements `e = (1,0)` and `f = (0,1)` in `R × S` are complementary
central idempotents: `e * e = e`, `f * f = f`, `e * f = 0`, `f * e = 0`, and `e + f = 1`.
For any `(R × S)`-module `M`, left multiplication by `e` and `f` gives idempotent
`(R × S)`-linear endomorphisms `eEnd` and `fEnd`. Their images `eSubmodule` and `fSubmodule`
are the complementary summands: they intersect trivially and span `M`. The projections
`eProj`, `fProj` and inclusions `eIncl`, `fIncl` assemble into the decomposition maps
`decomp : M → eM × fM` and `decompSymm : eM × fM → M`, inverse to each other, and the
equivalence `decompEquiv`. For an `(R × S)`-linear map, the induced maps `map_eSubmodule`,
`map_fSubmodule`, `map_eSubmodule_R`, and `map_fSubmodule_S` preserve the summands,
making the decomposition functorial and compatible with projections and inclusions.
-/

@[expose] public section

namespace ProdIdempotent

section Idempotents

variable (R S : Type*) [Ring R] [Ring S]

/-- `e = (1,0)` in `R × S`. -/
def e : R × S := (1, 0)

/-- `f = (0,1)` in `R × S`. -/
def f : R × S := (0, 1)

/-- First projection of `e = (1,0)` is `1`. -/
@[simp]
lemma e_fst : (e R S).1 = 1 := rfl

/-- Second projection of `e = (1,0)` is `0`. -/
@[simp]
lemma e_snd : (e R S).2 = 0 := rfl

/-- First projection of `f = (0,1)` is `0`. -/
@[simp]
lemma f_fst : (f R S).1 = 0 := rfl

/-- Second projection of `f = (0,1)` is `1`. -/
@[simp]
lemma f_snd : (f R S).2 = 1 := rfl

/-- `e` is idempotent: `e * e = e`. -/
@[simp]
lemma e_mul_e : e R S * e R S = e R S := by
  ext <;> simp [e]

/-- `f` is idempotent: `f * f = f`. -/
@[simp]
lemma f_mul_f : f R S * f R S = f R S := by
  ext <;> simp [f]

/-- `e` and `f` are orthogonal: `e * f = 0`. -/
@[simp]
lemma e_mul_f : e R S * f R S = 0 := by
  ext <;> simp [e, f]

/-- `f` and `e` are orthogonal: `f * e = 0`. -/
@[simp]
lemma f_mul_e : f R S * e R S = 0 := by
  ext <;> simp [e, f]

/-- `e + f = 1` in `R × S`. -/
lemma e_add_f : e R S + f R S = 1 := by
  ext <;> simp [e, f]

/-- `f + e = 1` in `R × S`. -/
lemma f_add_e : f R S + e R S = 1 := by
  ext <;> simp [e, f, add_comm]

/-- Right multiplication by `e` projects to the first coordinate. -/
@[simp]
lemma mul_e_eq (p : R × S) : p * e R S = (p.1, 0) := by
  ext
  · simp [e]
  · simp [e]

/-- Left multiplication by `e` projects to the first coordinate. -/
@[simp]
lemma e_mul_eq (p : R × S) : e R S * p = (p.1, 0) := by
  ext
  · simp [e]
  · simp [e]

/-- Right multiplication by `f` projects to the second coordinate. -/
@[simp]
lemma mul_f_eq (p : R × S) : p * f R S = (0, p.2) := by
  ext
  · simp [f]
  · simp [f]

/-- Left multiplication by `f` projects to the second coordinate. -/
@[simp]
lemma f_mul_eq (p : R × S) : f R S * p = (0, p.2) := by
  ext
  · simp [f]
  · simp [f]

/-- `e` commutes with every element of `R × S`. -/
lemma e_comm (p : R × S) : e R S * p = p * e R S := by
  simp

/-- `f` commutes with every element of `R × S`. -/
lemma f_comm (p : R × S) : f R S * p = p * f R S := by
  simp

/-- `e` is central in `R × S`. -/
lemma e_central : ∀ p : R × S, p * e R S = e R S * p := fun p => (e_comm R S p).symm

/-- `f` is central in `R × S`. -/
lemma f_central : ∀ p : R × S, p * f R S = f R S * p := fun p => (f_comm R S p).symm

/-- `e` is an idempotent element of `R × S`. -/
lemma isIdempotentElem_e : IsIdempotentElem (e R S) := by
  rw [IsIdempotentElem, e_mul_e]

/-- `f` is an idempotent element of `R × S`. -/
lemma isIdempotentElem_f : IsIdempotentElem (f R S) := by
  rw [IsIdempotentElem, f_mul_f]

end Idempotents

section Component

variable {R S : Type*} [Ring R] [Ring S]
variable {M : Type*} [AddCommGroup M] [Module (R × S) M]

/-- Left multiplication by `e = (1,0)` as an `(R × S)`-linear endomorphism. -/
def eEnd : M →ₗ[R × S] M where
  toFun m := (ProdIdempotent.e R S) • m
  map_add' x y := smul_add _ x y
  map_smul' c x := by
    calc
      (ProdIdempotent.e R S) • (c • x) = (ProdIdempotent.e R S * c) • x := by
        rw [mul_smul]
      _ = (c * ProdIdempotent.e R S) • x := by
        rw [ProdIdempotent.e_comm]
      _ = c • (ProdIdempotent.e R S) • x := by
        rw [mul_smul]

/-- Left multiplication by `f = (0,1)` as an `(R × S)`-linear endomorphism. -/
def fEnd : M →ₗ[R × S] M where
  toFun m := (ProdIdempotent.f R S) • m
  map_add' x y := smul_add _ x y
  map_smul' c x := by
    calc
      (ProdIdempotent.f R S) • (c • x) = (ProdIdempotent.f R S * c) • x := by
        rw [mul_smul]
      _ = (c * ProdIdempotent.f R S) • x := by
        rw [ProdIdempotent.f_comm]
      _ = c • (ProdIdempotent.f R S) • x := by
        rw [mul_smul]

/-- Applying `eEnd` is multiplication by `e`. -/
@[simp]
lemma eEnd_apply (m : M) :
    eEnd (R := R) (S := S) (M := M) m = ProdIdempotent.e R S • m := rfl

/-- Applying `fEnd` is multiplication by `f`. -/
@[simp]
lemma fEnd_apply (m : M) :
    fEnd (R := R) (S := S) (M := M) m = ProdIdempotent.f R S • m := rfl

/-- `eEnd` is idempotent as a linear map. -/
@[simp]
lemma eEnd_comp_eEnd :
    (eEnd (M := M) (R := R) (S := S)).comp eEnd = eEnd := by
  ext m
  change ProdIdempotent.e R S • (ProdIdempotent.e R S • m) = ProdIdempotent.e R S • m
  rw [← mul_smul, ProdIdempotent.e_mul_e]

/-- `fEnd` is idempotent as a linear map. -/
@[simp]
lemma fEnd_comp_fEnd :
    (fEnd (M := M) (R := R) (S := S)).comp fEnd = fEnd := by
  ext m
  change ProdIdempotent.f R S • (ProdIdempotent.f R S • m) = ProdIdempotent.f R S • m
  rw [← mul_smul, ProdIdempotent.f_mul_f]

/-- `eEnd` composed with `fEnd` is zero. -/
@[simp]
lemma eEnd_comp_fEnd :
    (eEnd (M := M) (R := R) (S := S)).comp fEnd = 0 := by
  ext m
  change ProdIdempotent.e R S • (ProdIdempotent.f R S • m) = 0
  rw [← mul_smul, ProdIdempotent.e_mul_f, zero_smul]

/-- `fEnd` composed with `eEnd` is zero. -/
@[simp]
lemma fEnd_comp_eEnd :
    (fEnd (M := M) (R := R) (S := S)).comp eEnd = 0 := by
  ext m
  change ProdIdempotent.f R S • (ProdIdempotent.e R S • m) = 0
  rw [← mul_smul, ProdIdempotent.f_mul_e, zero_smul]

/-- `eEnd + fEnd = id` as `(R × S)`-linear maps. -/
lemma eEnd_add_fEnd :
    eEnd (M := M) (R := R) (S := S) + fEnd = LinearMap.id := by
  ext m
  simp only [LinearMap.add_apply, LinearMap.id_apply, eEnd_apply, fEnd_apply]
  calc
    ProdIdempotent.e R S • m + ProdIdempotent.f R S • m
        = (ProdIdempotent.e R S + ProdIdempotent.f R S) • m := by rw [add_smul]
    _ = (1 : R × S) • m := by rw [ProdIdempotent.e_add_f]
    _ = m := by rw [one_smul]

/-- The `e = (1,0)`-component submodule of `M`. -/
def eSubmodule : Submodule (R × S) M :=
  LinearMap.range (eEnd (R := R) (S := S) (M := M))

/-- The `f = (0,1)`-component submodule of `M`. -/
def fSubmodule : Submodule (R × S) M :=
  LinearMap.range (fEnd (R := R) (S := S) (M := M))

/-- Membership in `eSubmodule` is fixed by `e`. -/
lemma mem_eSubmodule_iff (m : M) :
    m ∈ (eSubmodule (R := R) (S := S) (M := M)) ↔
      ProdIdempotent.e R S • m = m := by
  constructor
  · rintro ⟨n, hn⟩
    have hm : m = ProdIdempotent.e R S • n := hn.symm
    calc
      ProdIdempotent.e R S • m =
          ProdIdempotent.e R S • (ProdIdempotent.e R S • n) := by rw [hm]
      _ = (ProdIdempotent.e R S * ProdIdempotent.e R S) • n := by rw [mul_smul]
      _ = ProdIdempotent.e R S • n := by rw [ProdIdempotent.e_mul_e]
      _ = m := hm.symm
  · intro hm
    exact ⟨m, hm⟩

/-- Membership in `fSubmodule` is fixed by `f`. -/
lemma mem_fSubmodule_iff (m : M) :
    m ∈ (fSubmodule (R := R) (S := S) (M := M)) ↔
      ProdIdempotent.f R S • m = m := by
  constructor
  · rintro ⟨n, hn⟩
    have hm : m = ProdIdempotent.f R S • n := hn.symm
    calc
      ProdIdempotent.f R S • m =
          ProdIdempotent.f R S • (ProdIdempotent.f R S • n) := by rw [hm]
      _ = (ProdIdempotent.f R S * ProdIdempotent.f R S) • n := by rw [mul_smul]
      _ = ProdIdempotent.f R S • n := by rw [ProdIdempotent.f_mul_f]
      _ = m := hm.symm
  · intro hm
    exact ⟨m, hm⟩

/-- `e • m` lies in `eSubmodule`. -/
lemma e_smul_mem_eSubmodule (m : M) :
    ProdIdempotent.e R S • m ∈ (eSubmodule (R := R) (S := S) (M := M)) :=
  ⟨m, rfl⟩

/-- `f • m` lies in `fSubmodule`. -/
lemma f_smul_mem_fSubmodule (m : M) :
    ProdIdempotent.f R S • m ∈ (fSubmodule (R := R) (S := S) (M := M)) :=
  ⟨m, rfl⟩

/-- Elements of `eSubmodule` are fixed by `e`. -/
@[simp]
lemma e_smul_of_mem_eSubmodule {m : M}
    (hm : m ∈ (eSubmodule (R := R) (S := S) (M := M))) :
    ProdIdempotent.e R S • m = m :=
  (mem_eSubmodule_iff m).mp hm

/-- Elements of `fSubmodule` are fixed by `f`. -/
@[simp]
lemma f_smul_of_mem_fSubmodule {m : M}
    (hm : m ∈ (fSubmodule (R := R) (S := S) (M := M))) :
    ProdIdempotent.f R S • m = m :=
  (mem_fSubmodule_iff m).mp hm

/-- `f` annihilates `eSubmodule`. -/
lemma f_smul_of_mem_eSubmodule_eq_zero {m : M}
    (hm : m ∈ (eSubmodule (R := R) (S := S) (M := M))) :
    ProdIdempotent.f R S • m = 0 := by
  have he : ProdIdempotent.e R S • m = m := e_smul_of_mem_eSubmodule hm
  calc
    ProdIdempotent.f R S • m =
        ProdIdempotent.f R S • (ProdIdempotent.e R S • m) := by rw [he]
    _ = (ProdIdempotent.f R S * ProdIdempotent.e R S) • m := by rw [mul_smul]
    _ = (0 : R × S) • m := by rw [ProdIdempotent.f_mul_e]
    _ = 0 := by rw [zero_smul]

/-- `e` annihilates `fSubmodule`. -/
lemma e_smul_of_mem_fSubmodule_eq_zero {m : M}
    (hm : m ∈ (fSubmodule (R := R) (S := S) (M := M))) :
    ProdIdempotent.e R S • m = 0 := by
  have hf : ProdIdempotent.f R S • m = m := f_smul_of_mem_fSubmodule hm
  calc
    ProdIdempotent.e R S • m =
        ProdIdempotent.e R S • (ProdIdempotent.f R S • m) := by rw [hf]
    _ = (ProdIdempotent.e R S * ProdIdempotent.f R S) • m := by rw [mul_smul]
    _ = (0 : R × S) • m := by rw [ProdIdempotent.e_mul_f]
    _ = 0 := by rw [zero_smul]

/-- The two summand submodules intersect trivially. -/
lemma eSubmodule_inf_fSubmodule :
    (eSubmodule (R := R) (S := S) (M := M)) ⊓
      (fSubmodule (R := R) (S := S) (M := M)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro m hm
  obtain ⟨he, hf⟩ := Submodule.mem_inf.mp hm
  have h0 : ProdIdempotent.f R S • m = 0 := f_smul_of_mem_eSubmodule_eq_zero he
  have h1 : ProdIdempotent.f R S • m = m := f_smul_of_mem_fSubmodule hf
  rw [h0] at h1
  exact h1.symm

/-- The two summand submodules span the whole module. -/
lemma eSubmodule_sup_fSubmodule :
    (eSubmodule (R := R) (S := S) (M := M)) ⊔
      (fSubmodule (R := R) (S := S) (M := M)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro m
  have hmem_e :
      ProdIdempotent.e R S • m ∈ (eSubmodule (R := R) (S := S) (M := M)) :=
    e_smul_mem_eSubmodule m
  have hmem_f :
      ProdIdempotent.f R S • m ∈ (fSubmodule (R := R) (S := S) (M := M)) :=
    f_smul_mem_fSubmodule m
  have hm : m = ProdIdempotent.e R S • m + ProdIdempotent.f R S • m := by
    calc
      m = (1 : R × S) • m := by rw [one_smul]
      _ = (ProdIdempotent.e R S + ProdIdempotent.f R S) • m := by
        rw [ProdIdempotent.e_add_f]
      _ = ProdIdempotent.e R S • m + ProdIdempotent.f R S • m := by rw [add_smul]
  rw [hm]
  exact Submodule.add_mem_sup hmem_e hmem_f

-- R-module and S-module structures on the components

/-- `R`-action on `eSubmodule` via `(r,0)`. -/
instance instSMulR_eSubmodule :
    SMul R (eSubmodule (R := R) (S := S) (M := M)) where
  smul r x :=
    ⟨(r, (0 : S)) • (x : M),
      (eSubmodule (R := R) (S := S) (M := M)).smul_mem (r, (0 : S)) x.2⟩

/-- `S`-action on `fSubmodule` via `(0,s)`. -/
instance instSMulS_fSubmodule :
    SMul S (fSubmodule (R := R) (S := S) (M := M)) where
  smul s y :=
    ⟨((0 : R), s) • (y : M),
      (fSubmodule (R := R) (S := S) (M := M)).smul_mem ((0 : R), s) y.2⟩

/-- Coercion of the `R`-smul on `eSubmodule` is `(r,0)`-smul. -/
@[simp]
lemma coe_smulR_eSubmodule (r : R)
    (x : eSubmodule (R := R) (S := S) (M := M)) :
    (r • x).val = (r, (0 : S)) • (x : M) := rfl

/-- Coercion of the `S`-smul on `fSubmodule` is `(0,s)`-smul. -/
@[simp]
lemma coe_smulS_fSubmodule (s : S)
    (y : fSubmodule (R := R) (S := S) (M := M)) :
    (s • y).val = ((0 : R), s) • (y : M) := rfl

/-- `R`-module structure on `eSubmodule`. -/
instance instModuleR_eSubmodule :
    Module R (eSubmodule (R := R) (S := S) (M := M)) where
  one_smul x := by
    ext
    have hx : (x : M) ∈ (eSubmodule (R := R) (S := S) (M := M)) := x.2
    have he : ProdIdempotent.e R S • (x : M) = (x : M) :=
      e_smul_of_mem_eSubmodule hx
    change ((1 : R), (0 : S)) • (x : M) = (x : M)
    change ProdIdempotent.e R S • (x : M) = (x : M)
    exact he
  mul_smul r s x := by
    ext
    change (r * s, (0 : S)) • (x : M) = (r, (0 : S)) • ((s, (0 : S)) • (x : M))
    rw [← mul_smul]
    congr 1
    ext
    · simp
    · simp
  zero_smul x := by
    ext
    change (0, (0 : S)) • (x : M) = 0
    change (0 : R × S) • (x : M) = 0
    rw [zero_smul]
  add_smul r s x := by
    ext
    change (r + s, (0 : S)) • (x : M) =
      (r, (0 : S)) • (x : M) + (s, (0 : S)) • (x : M)
    rw [← add_smul]
    congr 1
    ext
    · simp
    · simp
  smul_add r x y := by
    ext
    change (r, (0 : S)) • ((x : M) + (y : M)) =
      (r, (0 : S)) • (x : M) + (r, (0 : S)) • (y : M)
    rw [smul_add]
  smul_zero r := by
    ext
    change (r, (0 : S)) • (0 : M) = 0
    rw [smul_zero]

/-- `S`-module structure on `fSubmodule`. -/
instance instModuleS_fSubmodule :
    Module S (fSubmodule (R := R) (S := S) (M := M)) where
  one_smul y := by
    ext
    have hy : (y : M) ∈ (fSubmodule (R := R) (S := S) (M := M)) := y.2
    have hf : ProdIdempotent.f R S • (y : M) = (y : M) :=
      f_smul_of_mem_fSubmodule hy
    change ((0 : R), (1 : S)) • (y : M) = (y : M)
    change ProdIdempotent.f R S • (y : M) = (y : M)
    exact hf
  mul_smul r s y := by
    ext
    change (0, r * s) • (y : M) = ((0 : R), r) • (((0 : R), s) • (y : M))
    rw [← mul_smul]
    congr 1
    ext
    · simp
    · simp
  zero_smul y := by
    ext
    change (0, (0 : S)) • (y : M) = 0
    change (0 : R × S) • (y : M) = 0
    rw [zero_smul]
  add_smul r s y := by
    ext
    change (0, r + s) • (y : M) =
      ((0 : R), r) • (y : M) + ((0 : R), s) • (y : M)
    rw [← add_smul]
    congr 1
    ext
    · simp
    · simp
  smul_add r x y := by
    ext
    change ((0 : R), r) • ((x : M) + (y : M)) =
      ((0 : R), r) • (x : M) + ((0 : R), r) • (y : M)
    rw [smul_add]
  smul_zero r := by
    ext
    change ((0 : R), r) • (0 : M) = 0
    rw [smul_zero]

/-- Inclusion `eM → M` as `(R × S)`-linear map. -/
def eIncl : eSubmodule (R := R) (S := S) (M := M) →ₗ[R × S] M :=
  (eSubmodule (R := R) (S := S) (M := M)).subtype

/-- Inclusion `fM → M` as `(R × S)`-linear map. -/
def fIncl : fSubmodule (R := R) (S := S) (M := M) →ₗ[R × S] M :=
  (fSubmodule (R := R) (S := S) (M := M)).subtype

/-- Projection `M → eM` as `(R × S)`-linear map, `m ↦ e • m`. -/
def eProj : M →ₗ[R × S] eSubmodule (R := R) (S := S) (M := M) where
  toFun m := ⟨ProdIdempotent.e R S • m, e_smul_mem_eSubmodule m⟩
  map_add' x y := by
    ext
    change ProdIdempotent.e R S • (x + y) =
      ProdIdempotent.e R S • x + ProdIdempotent.e R S • y
    rw [smul_add]
  map_smul' c x := by
    ext
    calc
      ProdIdempotent.e R S • (c • x) = (ProdIdempotent.e R S * c) • x := by
        rw [mul_smul]
      _ = (c * ProdIdempotent.e R S) • x := by rw [ProdIdempotent.e_comm]
      _ = c • ProdIdempotent.e R S • x := by rw [mul_smul]

/-- Projection `M → fM` as `(R × S)`-linear map, `m ↦ f • m`. -/
def fProj : M →ₗ[R × S] fSubmodule (R := R) (S := S) (M := M) where
  toFun m := ⟨ProdIdempotent.f R S • m, f_smul_mem_fSubmodule m⟩
  map_add' x y := by
    ext
    change ProdIdempotent.f R S • (x + y) =
      ProdIdempotent.f R S • x + ProdIdempotent.f R S • y
    rw [smul_add]
  map_smul' c x := by
    ext
    calc
      ProdIdempotent.f R S • (c • x) = (ProdIdempotent.f R S * c) • x := by
        rw [mul_smul]
      _ = (c * ProdIdempotent.f R S) • x := by rw [ProdIdempotent.f_comm]
      _ = c • ProdIdempotent.f R S • x := by rw [mul_smul]

/-- `eIncl ∘ eProj` is multiplication by `e`. -/
@[simp]
lemma eIncl_eProj (m : M) :
    eIncl (R := R) (S := S) (eProj (R := R) (S := S) (M := M) m) =
      ProdIdempotent.e R S • m := rfl

/-- `fIncl ∘ fProj` is multiplication by `f`. -/
@[simp]
lemma fIncl_fProj (m : M) :
    fIncl (R := R) (S := S) (fProj (R := R) (S := S) (M := M) m) =
      ProdIdempotent.f R S • m := rfl

/-- `eProj` is a retraction of `eIncl`. -/
@[simp]
lemma eProj_eIncl (x : eSubmodule (R := R) (S := S) (M := M)) :
    eProj (R := R) (S := S) (eIncl (R := R) (S := S) x) = x := by
  ext
  change ProdIdempotent.e R S • (x : M) = (x : M)
  exact e_smul_of_mem_eSubmodule x.2

/-- `fProj` is a retraction of `fIncl`. -/
@[simp]
lemma fProj_fIncl (y : fSubmodule (R := R) (S := S) (M := M)) :
    fProj (R := R) (S := S) (fIncl (R := R) (S := S) y) = y := by
  ext
  change ProdIdempotent.f R S • (y : M) = (y : M)
  exact f_smul_of_mem_fSubmodule y.2

/-- `fProj` vanishes on `eSubmodule`. -/
@[simp]
lemma fProj_eIncl (x : eSubmodule (R := R) (S := S) (M := M)) :
    fProj (R := R) (S := S) (eIncl (R := R) (S := S) x) = 0 := by
  ext
  change ProdIdempotent.f R S • (x : M) = 0
  exact f_smul_of_mem_eSubmodule_eq_zero x.2

/-- `eProj` vanishes on `fSubmodule`. -/
@[simp]
lemma eProj_fIncl (y : fSubmodule (R := R) (S := S) (M := M)) :
    eProj (R := R) (S := S) (fIncl (R := R) (S := S) y) = 0 := by
  ext
  exact e_smul_of_mem_fSubmodule_eq_zero y.2

/-- Forward decomposition map `M → eM × fM`, `m ↦ (e • m, f • m)`. -/
def decomp :
    M →ₗ[R × S] (eSubmodule (R := R) (S := S) (M := M) ×
      fSubmodule (R := R) (S := S) (M := M)) where
  toFun m := (eProj m, fProj m)
  map_add' x y := by
    have he := map_add (eProj (R := R) (S := S) (M := M)) x y
    have hf := map_add (fProj (R := R) (S := S) (M := M)) x y
    simp only [Prod.mk_add_mk]
    ext
    · exact congrArg Subtype.val he
    · exact congrArg Subtype.val hf
  map_smul' c x := by
    have he := map_smul (eProj (R := R) (S := S) (M := M)) c x
    have hf := map_smul (fProj (R := R) (S := S) (M := M)) c x
    simp only [Prod.smul_mk]
    ext
    · exact congrArg Subtype.val he
    · exact congrArg Subtype.val hf

/-- Inverse decomposition map `eM × fM → M`, addition. -/
def decompSymm :
    (eSubmodule (R := R) (S := S) (M := M) ×
      fSubmodule (R := R) (S := S) (M := M)) →ₗ[R × S] M where
  toFun p := p.1.val + p.2.val
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    have h1 : (x.1 + y.1).val = x.1.val + y.1.val := rfl
    have h2 : (x.2 + y.2).val = x.2.val + y.2.val := rfl
    calc
      (x.1 + y.1).val + (x.2 + y.2).val =
          x.1.val + y.1.val + (x.2.val + y.2.val) := by rw [h1, h2]
      _ = x.1.val + x.2.val + (y.1.val + y.2.val) := by abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    have he : (c • x.1).val = c • x.1.val := rfl
    have hf : (c • x.2).val = c • x.2.val := rfl
    calc
      (c • x.1).val + (c • x.2).val =
          c • x.1.val + c • x.2.val := by rw [he, hf]
      _ = c • (x.1.val + x.2.val) := by rw [← smul_add]

/-- `decomp` sends `m` to `(e • m, f • m)`. -/
@[simp]
lemma decomp_apply (m : M) :
    decomp (R := R) (S := S) (M := M) m =
      (eProj (M := M) m, fProj (M := M) m) := rfl

/-- `decompSymm` on `(x,y)` is `x + y`. -/
@[simp]
lemma decompSymm_apply (x : eSubmodule (R := R) (S := S) (M := M))
    (y : fSubmodule (R := R) (S := S) (M := M)) :
    decompSymm (M := M) (x, y) = x.val + y.val := rfl

/-- `decompSymm` on `p` is `p.1 + p.2`. -/
@[simp]
lemma decompSymm_apply' (p :
    eSubmodule (R := R) (S := S) (M := M) ×
      fSubmodule (R := R) (S := S) (M := M)) :
    decompSymm (M := M) p = p.1.val + p.2.val := rfl

/-- `decompSymm ∘ decomp = id`. -/
lemma decompSymm_comp_decomp :
    (decompSymm (R := R) (S := S) (M := M)).comp
        (decomp (R := R) (S := S) (M := M)) = LinearMap.id := by
  ext m
  simp only [LinearMap.comp_apply, LinearMap.id_apply, decomp_apply, decompSymm_apply]
  calc
    ProdIdempotent.e R S • m + ProdIdempotent.f R S • m
        = (ProdIdempotent.e R S + ProdIdempotent.f R S) • m := by rw [add_smul]
    _ = (1 : R × S) • m := by rw [ProdIdempotent.e_add_f]
    _ = m := by rw [one_smul]

/-- `decomp ∘ decompSymm = id`. -/
lemma decomp_comp_decompSymm :
    (decomp (R := R) (S := S) (M := M)).comp
        (decompSymm (R := R) (S := S) (M := M)) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hx : ProdIdempotent.e R S • x.val = x.val :=
    e_smul_of_mem_eSubmodule x.2
  have hy_e : ProdIdempotent.e R S • y.val = 0 :=
    e_smul_of_mem_fSubmodule_eq_zero y.2
  have hx_f : ProdIdempotent.f R S • x.val = 0 :=
    f_smul_of_mem_eSubmodule_eq_zero x.2
  have hy : ProdIdempotent.f R S • y.val = y.val :=
    f_smul_of_mem_fSubmodule y.2
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    decompSymm_apply, decomp_apply]
  apply Prod.ext
  · apply Subtype.ext
    calc
      ProdIdempotent.e R S • (x.val + y.val)
          = ProdIdempotent.e R S • x.val +
            ProdIdempotent.e R S • y.val := by rw [smul_add]
      _ = x.val + 0 := by rw [hx, hy_e]
      _ = x.val := by rw [add_zero]
  · apply Subtype.ext
    calc
      ProdIdempotent.f R S • (x.val + y.val)
          = ProdIdempotent.f R S • x.val +
            ProdIdempotent.f R S • y.val := by rw [smul_add]
      _ = 0 + y.val := by rw [hx_f, hy]
      _ = y.val := by rw [zero_add]

/-- The canonical `(R × S)`-linear equivalence `M ≃ eM × fM`. -/
def decompEquiv :
    M ≃ₗ[R × S] (eSubmodule (R := R) (S := S) (M := M) ×
      fSubmodule (R := R) (S := S) (M := M)) :=
  LinearEquiv.ofLinearMap
    (decomp (R := R) (S := S) (M := M))
    (decompSymm (R := R) (S := S) (M := M))
    (decomp_comp_decompSymm (R := R) (S := S) (M := M))
    (decompSymm_comp_decomp (R := R) (S := S) (M := M))

/-- `decompEquiv` sends `m` to `(e • m, f • m)`. -/
@[simp]
lemma decompEquiv_apply (m : M) :
    decompEquiv (R := R) (S := S) (M := M) m =
      (eProj (M := M) m, fProj (M := M) m) := rfl

/-- Inverse of `decompEquiv` on `(x,y)` is `x + y`. -/
@[simp]
lemma decompEquiv_symm_apply (x : eSubmodule (R := R) (S := S) (M := M))
    (y : fSubmodule (R := R) (S := S) (M := M)) :
    (decompEquiv (R := R) (S := S) (M := M)).symm (x, y) =
      x.val + y.val := rfl

/-- Inverse of `decompEquiv` on `p` is `p.1 + p.2`. -/
@[simp]
lemma decompEquiv_symm_apply' (p :
    eSubmodule (R := R) (S := S) (M := M) ×
      fSubmodule (R := R) (S := S) (M := M)) :
    (decompEquiv (R := R) (S := S) (M := M)).symm p =
      p.1.val + p.2.val := rfl

end Component

section Functoriality

variable {R S : Type*} [Ring R] [Ring S]
variable {M N : Type*} [AddCommGroup M] [Module (R × S) M]
  [AddCommGroup N] [Module (R × S) N]

/-- An `(R × S)`-linear map commutes with `e • _`. -/
lemma LinearMap.map_e_smul (f : M →ₗ[R × S] N) (m : M) :
    f (ProdIdempotent.e R S • m) = ProdIdempotent.e R S • f m := by
  rw [← map_smul]

/-- An `(R × S)`-linear map commutes with `f • _`. -/
lemma LinearMap.map_f_smul (f : M →ₗ[R × S] N) (m : M) :
    f (ProdIdempotent.f R S • m) = ProdIdempotent.f R S • f m := by
  rw [← map_smul]

/-- An `(R × S)`-linear map preserves `eSubmodule` membership. -/
lemma LinearMap.map_mem_eSubmodule (f : M →ₗ[R × S] N) {m : M}
    (hm : m ∈ (eSubmodule (R := R) (S := S) (M := M))) :
    f m ∈ (eSubmodule (R := R) (S := S) (M := N)) := by
  rw [mem_eSubmodule_iff] at hm ⊢
  calc
    ProdIdempotent.e R S • f m = f (ProdIdempotent.e R S • m) := by rw [← map_smul]
    _ = f m := by rw [hm]

/-- An `(R × S)`-linear map preserves `fSubmodule` membership. -/
lemma LinearMap.map_mem_fSubmodule (f : M →ₗ[R × S] N) {m : M}
    (hm : m ∈ (fSubmodule (R := R) (S := S) (M := M))) :
    f m ∈ (fSubmodule (R := R) (S := S) (M := N)) := by
  rw [mem_fSubmodule_iff] at hm ⊢
  calc
    ProdIdempotent.f R S • f m = f (ProdIdempotent.f R S • m) := by rw [← map_smul]
    _ = f m := by rw [hm]

/-- Induced map on `e`-components from an `(R × S)`-linear map. -/
def map_eSubmodule (f : M →ₗ[R × S] N) :
    eSubmodule (R := R) (S := S) (M := M) →ₗ[R × S]
      eSubmodule (R := R) (S := S) (M := N) where
  toFun x :=
    ⟨f x.val, LinearMap.map_mem_eSubmodule (R := R) (S := S) f x.2⟩
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' c x := by
    ext
    simp [map_smul]

/-- Induced map on `f`-components from an `(R × S)`-linear map. -/
def map_fSubmodule (f : M →ₗ[R × S] N) :
    fSubmodule (R := R) (S := S) (M := M) →ₗ[R × S]
      fSubmodule (R := R) (S := S) (M := N) where
  toFun y :=
    ⟨f y.val, LinearMap.map_mem_fSubmodule (R := R) (S := S) f y.2⟩
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' c x := by
    ext
    simp [map_smul]

/-- Induced map on `e`-components as `R`-linear map. -/
def map_eSubmodule_R (f : M →ₗ[R × S] N) :
    eSubmodule (R := R) (S := S) (M := M) →ₗ[R]
      eSubmodule (R := R) (S := S) (M := N) where
  toFun x :=
    ⟨f x.val, LinearMap.map_mem_eSubmodule (R := R) (S := S) f x.2⟩
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' r x := by
    ext
    change f ((r, (0 : S)) • (x : M)) = (r, (0 : S)) • f (x : M)
    exact map_smul f (r, (0 : S)) _

/-- Induced map on `f`-components as `S`-linear map. -/
def map_fSubmodule_S (f : M →ₗ[R × S] N) :
    fSubmodule (R := R) (S := S) (M := M) →ₗ[S]
      fSubmodule (R := R) (S := S) (M := N) where
  toFun y :=
    ⟨f y.val, LinearMap.map_mem_fSubmodule (R := R) (S := S) f y.2⟩
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' s y := by
    ext
    change f (((0 : R), s) • (y : M)) = ((0 : R), s) • f (y : M)
    exact map_smul f ((0 : R), s) _

/-- `eProj` after an `(R × S)`-map equals the induced `e`-map after `eProj`. -/
@[simp]
lemma eProj_comp_map (f : M →ₗ[R × S] N) :
    (eProj (R := R) (S := S) (M := N)).comp f =
      (map_eSubmodule (R := R) (S := S) f).comp
        (eProj (R := R) (S := S) (M := M)) := by
  ext m : 2
  simp only [LinearMap.comp_apply, eProj, map_eSubmodule]
  change ProdIdempotent.e R S • f m = f (ProdIdempotent.e R S • m)
  rw [← map_smul]

/-- `fProj` after an `(R × S)`-map equals the induced `f`-map after `fProj`. -/
@[simp]
lemma fProj_comp_map (f : M →ₗ[R × S] N) :
    (fProj (R := R) (S := S) (M := N)).comp f =
      (map_fSubmodule (R := R) (S := S) f).comp
        (fProj (R := R) (S := S) (M := M)) := by
  ext m : 2
  simp only [LinearMap.comp_apply, fProj, map_fSubmodule]
  change ProdIdempotent.f R S • f m = f (ProdIdempotent.f R S • m)
  rw [← map_smul]

/-- An `(R × S)`-map after `eIncl` equals `eIncl` after the induced `e`-map. -/
@[simp]
lemma map_comp_eIncl (f : M →ₗ[R × S] N) :
    f.comp (eIncl (R := R) (S := S) (M := M)) =
      (eIncl (R := R) (S := S) (M := N)).comp
        (map_eSubmodule (R := R) (S := S) f) := by
  ext x
  rfl

/-- An `(R × S)`-map after `fIncl` equals `fIncl` after the induced `f`-map. -/
@[simp]
lemma map_comp_fIncl (f : M →ₗ[R × S] N) :
    f.comp (fIncl (R := R) (S := S) (M := M)) =
      (fIncl (R := R) (S := S) (M := N)).comp
        (map_fSubmodule (R := R) (S := S) f) := by
  ext y
  rfl

/-- The decomposition `decomp` is natural in the `(R × S)`-module. -/
lemma decomp_natural (f : M →ₗ[R × S] N) :
    (decomp (R := R) (S := S) (M := N)).comp f =
      (LinearMap.prodMap
          (map_eSubmodule (R := R) (S := S) f)
          (map_fSubmodule (R := R) (S := S) f)).comp
        (decomp (R := R) (S := S) (M := M)) := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, decomp_apply, LinearMap.prodMap_apply]
  have he : eProj (R := R) (S := S) (M := N) (f m) =
      map_eSubmodule (R := R) (S := S) f (eProj (R := R) (S := S) (M := M) m) := by
    calc
      eProj (M := N) (f m) = (eProj (M := N).comp f) m := rfl
      _ = ((map_eSubmodule (R := R) (S := S) f).comp
          (eProj (R := R) (S := S) (M := M))) m := by rw [eProj_comp_map]
      _ = map_eSubmodule f (eProj m) := rfl
  have hf : fProj (R := R) (S := S) (M := N) (f m) =
      map_fSubmodule (R := R) (S := S) f (fProj (R := R) (S := S) (M := M) m) := by
    calc
      fProj (M := N) (f m) = (fProj (M := N).comp f) m := rfl
      _ = ((map_fSubmodule (R := R) (S := S) f).comp
          (fProj (R := R) (S := S) (M := M))) m := by rw [fProj_comp_map]
      _ = map_fSubmodule f (fProj m) := rfl
  exact Prod.mk_inj.mpr ⟨he, hf⟩

end Functoriality

end ProdIdempotent
