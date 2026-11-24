/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.Basis.FiniteFiltration
public import MathlibExt.LinearAlgebra.Determinant.FiniteFiltration

/-!
# Determinants of filtration-unipotent endomorphisms

Let

```text
F 0 ≤ F 1 ≤ ... ≤ F n = M
```

be a finite filtration from zero to the whole module.  Choose a basis of
every successive quotient and assemble them into
`Module.Basis.ofFiltration`.  This file proves that an endomorphism has
determinant one if it fixes every assembled graded basis vector modulo the
preceding stage.

More precisely, write `B` for the assembled basis and suppose

```text
U (B ⟨i,a⟩) - B ⟨i,a⟩ ∈ F i
```

for every grade `i` and graded basis index `a`.  Then `U.det = 1`.

## Informal proof

### Prefix agreement

For `j ≤ n`, an index `i : Fin j` also defines an index of the final
assembled basis.  Repeated use of `Module.Basis.ofFiltrationStage_castSucc`
shows that the `i`-th vector of the stage-`j` basis and the corresponding
ambient vector have the same underlying element of `M`.  The proof is by
induction on the final cutoff.  At a successor cutoff, either `j` is already
below the previous cutoff, in which case apply the induction hypothesis and
one cast-successor identity, or `j` is the new final cutoff, in which case
the statement is reflexive.

### Derived stage stability

Fix `j ≤ n` and expand `x : F j` in the explicit basis
`ofFiltrationStage ... j`.  For a basis vector introduced in grade `i < j`,
prefix agreement identifies its ambient value with `B ⟨i,a⟩`.  The
hypothesis places its error under `U` in `F i`, hence in `F j`; the vector
itself already belongs to `F j`.  Thus its image under `U` belongs to `F j`.
Linearity and the finite basis expansion prove `F j ≤ (F j).comap U`.

### Adjacent quotients

Restrict `U` to every stable stage.  For adjacent stages, identify `F i`
with its copy inside `F (i+1)` by
`Submodule.comapSubtypeEquivOfLe`.  The restricted maps intertwine on
underlying values, producing a `LinearMap.InvariantExtension`.

The quotient basis vector `b i a` is represented by
`Module.Basis.ofFiltrationStageVector ... i a`.  Its ambient value is exactly
the assembled grade-`i` basis vector.  The error hypothesis therefore says
that the induced quotient map fixes this representative modulo `F i`.
Basis extensionality proves that every successive quotient map is
`LinearMap.id`; its determinant is one.

### Determinant product

The explicit stage bases and quotient bases install finite-free structures
on all modules used by
`LinearMap.det_eq_prod_graded_of_bottom_subsingleton`.  The bottom equality
`F 0 = ⊥` makes the first stage subsingleton.  The determinant product is
therefore a product of ones.  Finally, the canonical equivalence `F n ≃ M`
conjugates the last restricted endomorphism to `U`, so determinant invariance
under conjugacy gives `U.det = 1`.

The proof includes `n = 0`: then the bottom is also the top, so the ambient
module is subsingleton and the empty determinant product is one.  Empty
graded index types are harmless.  No field hypothesis is used.

## API novelty

The closest existing APIs are:

* `Module.Basis.ofFiltrationStage_castSucc` and
  `Module.Basis.ofFiltrationStageVector_mk`, which provide the exact basis
  representatives but do not prove stability of an arbitrary endomorphism;
* `LinearMap.det_eq_prod_graded_of_bottom_subsingleton`, which factors a
  determinant once invariant stages and quotient maps are already supplied;
* matrix triangular determinant lemmas, which would require an additional
  order on the dependent basis index and would duplicate the filtration
  infrastructure.

The theorem below is therefore the missing bridge: it derives both stage
stability and graded identity from the basis-level error hypothesis.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Module
open scoped BigOperators

universe uR uM uι

namespace Module.Basis

variable {R : Type uR} {M : Type uM} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable {κ : ℕ → Type uι}

/-- Passing an early filtration basis vector through any number of later
stages does not change its underlying ambient value. -/
private theorem coe_ofFiltrationStage_eq_of_le
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    {j : ℕ} (hj : j ≤ n) (i : Fin j) (a : κ i.val) :
    ((ofFiltrationStage F hzero κ j
        (fun k => hF (k.castLE hj))
        (fun k => b (k.castLE hj)) ⟨i, a⟩ : F j) : M) =
      ((ofFiltrationStage F hzero κ n hF b
        ⟨i.castLE hj, a⟩ : F n) : M) := by
  induction n with
  | zero => exact Fin.elim0 (i.castLE hj)
  | succ n ih =>
      by_cases hjn : j ≤ n
      · calc
          _ = ((ofFiltrationStage F hzero κ n
                (fun k => hF k.castSucc)
                (fun k => b k.castSucc)
                ⟨i.castLE hjn, a⟩ : F n) : M) :=
            ih (fun k => hF k.castSucc) (fun k => b k.castSucc) hjn
          _ = ((ofFiltrationStage F hzero κ (n + 1) hF b
                ⟨i.castLE hj, a⟩ : F (n + 1)) : M) := by
            symm
            simpa using ofFiltrationStage_castSucc F hzero κ n hF b
              (i.castLE hjn) a
      · have hjeq : j = n + 1 := by omega
        subst j
        rfl

private theorem filtration_mono_of_succ
    (F : ℕ → Submodule R M) (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : F i ≤ F j := by
  revert hj
  refine Nat.le_induction (m := i)
    (P := fun j _ => j ≤ n → F i ≤ F j) ?_ ?_ j hij
  · intro _
    exact le_rfl
  · intro k hik ih hk1n
    exact (ih (Nat.le_trans (Nat.le_succ k) hk1n)).trans
      (hF ⟨k, Nat.lt_of_succ_le hk1n⟩)

/-- A vector in a prefix filtration basis agrees in `M` with the
corresponding vector of the final assembled basis. -/
theorem ofFiltration_apply_eq_ofFiltrationStage
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    {j : ℕ} (hj : j ≤ n) (i : Fin j) (a : κ i.val) :
    ofFiltration F hzero κ n hF b htop ⟨i.castLE hj, a⟩ =
      ((ofFiltrationStage F hzero κ j
        (fun k => hF (k.castLE hj))
        (fun k => b (k.castLE hj)) ⟨i, a⟩ : F j) : M) := by
  rw [ofFiltration_apply]
  exact (coe_ofFiltrationStage_eq_of_le F hzero n hF b hj i a).symm

/-- The basis-level condition `U b - b ∈ F i` on every vector introduced at
grade `i` forces every filtration stage to be `U`-stable. -/
theorem ofFiltration_stable
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    (U : M →ₗ[R] M)
    (hU : ∀ i : Fin n, ∀ a : κ i.val,
      U (ofFiltration F hzero κ n hF b htop ⟨i, a⟩) -
          ofFiltration F hzero κ n hF b htop ⟨i, a⟩ ∈ F i.val)
    [∀ i : Fin n, Finite (κ i.val)]
    (j : ℕ) (hj : j ≤ n) : F j ≤ (F j).comap U := by
  let _ : ∀ i : Fin n, Fintype (κ i.val) := fun _ => Fintype.ofFinite _
  let _ : ∀ i : Fin j, Fintype (κ i.val) := fun i =>
    inferInstanceAs (Fintype (κ (i.castLE hj).val))
  let bj := ofFiltrationStage F hzero κ j
    (fun k => hF (k.castLE hj)) (fun k => b (k.castLE hj))
  intro x hx
  let xj : F j := ⟨x, hx⟩
  have hsum := bj.sum_repr xj
  have hsumM := congrArg (fun z : F j => (z : M)) hsum
  have hcoe :
      (((∑ p, (bj.repr xj) p • bj p : F j) : F j) : M) =
        ∑ p, (bj.repr xj) p • (bj p : M) := by
    change (F j).subtype (∑ p, (bj.repr xj) p • bj p) = _
    rw [map_sum]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro p _
    rfl
  have hsumM' :
      (∑ p, (bj.repr xj) p • (bj p : M)) = (xj : M) :=
    hcoe.symm.trans hsumM
  change U (xj : M) ∈ F j
  rw [← hsumM', map_sum]
  exact Submodule.sum_mem _ fun p _ => by
    rw [map_smul]
    apply Submodule.smul_mem
    have hpref := ofFiltration_apply_eq_ofFiltrationStage
      F hzero n hF b htop hj p.1 p.2
    have herr := hU (p.1.castLE hj) p.2
    rw [hpref] at herr
    have herrj : U (bj p : M) - (bj p : M) ∈ F j :=
      filtration_mono_of_succ F n hF (Nat.le_of_lt p.1.isLt) hj herr
    rw [← sub_add_cancel (U (bj p : M)) (bj p : M)]
    exact Submodule.add_mem _ herrj (bj p).property

end Module.Basis

namespace LinearMap

open Module.Basis

variable {R : Type uR} {M : Type uM} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable {κ : ℕ → Type uι}

/-- An endomorphism that fixes each assembled filtration-basis vector modulo
the preceding filtration stage has determinant one.  Stage stability and
identity on the successive quotients are conclusions of the proof, not
inputs. -/
theorem det_eq_one_of_sub_mem_ofFiltration
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    (U : M →ₗ[R] M)
    (hU : ∀ i : Fin n, ∀ a : κ i.val,
      U (ofFiltration F hzero κ n hF b htop ⟨i, a⟩) -
          ofFiltration F hzero κ n hF b htop ⟨i, a⟩ ∈ F i.val)
    [∀ i : Fin n, Finite (κ i.val)] :
    U.det = 1 := by
  let _ : ∀ i : Fin n, Fintype (κ i.val) := fun _ => Fintype.ofFinite _
  let B := ofFiltration F hzero κ n hF b htop
  let _ : Module.Free R M := Module.Free.of_basis B
  let _ : Module.Finite R M := Module.Finite.of_basis B
  let stageLE : ∀ j : Fin (n + 1), j.val ≤ n := fun j =>
    Nat.lt_succ_iff.mp j.isLt
  let stageBasis (j : Fin (n + 1)) :
      Basis (FiltrationIndex κ j.val) R (F j.val) :=
    ofFiltrationStage F hzero κ j.val
      (fun k => hF (k.castLE (stageLE j)))
      (fun k => b (k.castLE (stageLE j)))
  let _ : ∀ j : Fin (n + 1), Fintype (FiltrationIndex κ j.val) := fun j => by
    let _ : ∀ i : Fin j.val, Fintype (κ i.val) := fun i =>
      inferInstanceAs (Fintype (κ (i.castLE (stageLE j)).val))
    infer_instance
  let _ : ∀ j : Fin (n + 1), Module.Free R (F j.val) := fun j =>
    Module.Free.of_basis (stageBasis j)
  let _ : ∀ j : Fin (n + 1), Module.Finite R (F j.val) := fun j =>
    Module.Finite.of_basis (stageBasis j)
  let stable (j : Fin (n + 1)) : F j.val ≤ (F j.val).comap U :=
    ofFiltration_stable F hzero n hF b htop U hU j.val (stageLE j)
  let endomorphism (j : Fin (n + 1)) : F j.val →ₗ[R] F j.val :=
    U.restrict (stable j)
  let step (i : Fin n) :
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ) :=
    { submodule := (F i.val).comap (F (i.val + 1)).subtype
      stable := by
        intro x hx
        change U (x : M) ∈ F i.val
        exact stable i.castSucc hx
      equiv := (Submodule.comapSubtypeEquivOfLe (hF i)).symm
      intertwines := by
        apply LinearMap.ext
        intro x
        rfl }
  have hquotient (i : Fin n) :
      (step i).quotientMap = LinearMap.id := by
    apply (b i).ext
    intro a
    rw [← ofFiltrationStageVector_mk F hzero κ n hF b i a]
    rw [InvariantExtension.quotientMap_mk]
    apply (Submodule.Quotient.eq _).mpr
    change U
        ((ofFiltrationStageVector F hzero κ n hF b i a : F (i.val + 1)) : M) -
      ((ofFiltrationStageVector F hzero κ n hF b i a : F (i.val + 1)) : M) ∈
        F i.val
    simpa only [ofFiltrationStageVector, ofFiltration_apply] using hU i a
  let _ : Subsingleton (F (0 : Fin (n + 1)).val) := by
    change Subsingleton (F 0)
    rw [hzero]
    infer_instance
  have hdetStage : (endomorphism (Fin.last n)).det = 1 := by
    rw [det_eq_prod_graded_of_bottom_subsingleton
      endomorphism step (fun i => Module.Free.of_basis (b i))]
    simp only [hquotient, LinearMap.det_id, Finset.prod_const_one]
  let eTop : F n ≃ₗ[R] M :=
    (LinearEquiv.ofEq (F n) ⊤ htop).trans Submodule.topEquiv
  have hconj : eTop.conj (endomorphism (Fin.last n)) = U := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eTop.surjective x
    rfl
  calc
    U.det = (eTop.conj (endomorphism (Fin.last n))).det := by rw [hconj]
    _ = (endomorphism (Fin.last n)).det := by
      change LinearMap.det
          (((eTop : F n →ₗ[R] M) ∘ₗ endomorphism (Fin.last n)) ∘ₗ
            (eTop.symm : M →ₗ[R] F n)) =
        LinearMap.det (endomorphism (Fin.last n))
      exact LinearMap.det_conj (endomorphism (Fin.last n)) eTop
    _ = 1 := hdetStage

end LinearMap

end
