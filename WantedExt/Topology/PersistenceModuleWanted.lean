/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Topology.TDA.PersistenceModule
public import MathlibExt.Topology.TDA.PersistenceConverseStability
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Wanted: structure and stability of persistence modules

The central theorems of the algebraic theory of persistence, stated with the definitions of
`MathlibExt.Topology.TDA.PersistenceModule`; their proofs are deferred.

* Interval decomposition of pointwise finite-dimensional modules over `ℝ`
  (Crawley-Boevey 2015, Thm. 1.1) and of tame modules over `ℕ` into finitely many bars
  (Carlsson, *Topology and data*, Prop. 2.12; Zomorodian–Carlsson 2005).
* Uniqueness of the barcode (Krull–Remak–Schmidt–Azumaya, as in Chazal–de Silva–Glisse–Oudot,
  Thm. 1.3).
* Algebraic stability (`d_b ≤ d_i`, Chazal–de Silva–Glisse–Oudot, Thm. 4.11).
-/

@[expose] public section

open CategoryTheory Limits MathlibExt.Topology.TDA

universe u

namespace MathlibExt.Topology.PersistenceModuleWanted

variable (k : Type u) [Field k]

/-- **Crawley-Boevey's decomposition theorem.** Every pointwise finite-dimensional persistence
module `V : ℝ ⥤ ModuleCat k` (each `V t` finite-dimensional) is isomorphic to a direct sum of
interval modules `k_I`, `I` ranging over a family of nonempty order-connected subsets of `ℝ`
(W. Crawley-Boevey, *Decomposition of pointwise finite-dimensional persistence modules*,
J. Algebra Appl. 14 (2015), arXiv:1210.0819, Thm. 1.1, for any totally ordered index set with a
countable dense subset; here the index set is `ℝ`). The family of intervals is the barcode. -/
theorem_wanted exists_iso_sigma_intervalModule (V : ℝ ⥤ ModuleCat.{u} k)
    (hV : ∀ t, FiniteDimensional k (V.obj t)) :
    ∃ (ι : Type u) (I : ι → Set ℝ) (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected),
      Nonempty (V ≅ ∐ fun i => intervalModule k (I i) (hI i).2)

/-- **Barcodes of tame `ℕ`-persistence modules (Zomorodian–Carlsson).** A tame `ℕ`-persistence
module (every `V n` finite-dimensional and the structure maps `V n ⟶ V (n + 1)` isomorphisms for
all large `n`) is isomorphic to a finite direct sum of interval modules `U(m, n)`, `m ≤ n ≤ ∞`,
i.e. of interval modules of nonempty order-connected subsets of `ℕ` (G. Carlsson, *Topology and
data*, Bull. AMS 46 (2009), Prop. 2.12, from Prop. 2.11 and the structure theorem for finitely
generated graded `k[t]`-modules, Thm. 2.10; A. Zomorodian and G. Carlsson, *Computing persistent
homology*, Discrete Comput. Geom. 33 (2005)). -/
theorem_wanted exists_iso_sigma_intervalModule_nat_of_tame (V : ℕ ⥤ ModuleCat.{u} k)
    (hV : ∀ n, FiniteDimensional k (V.obj n))
    (htame : ∃ N, ∀ n, N ≤ n → IsIso (V.map (homOfLE (Nat.le_succ n)))) :
    ∃ (ι : Type u) (_ : Finite ι) (I : ι → Set ℕ)
      (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected),
      Nonempty (V ≅ ∐ fun i => intervalModule k (I i) (hI i).2)

/-- **The barcode is unique (Krull–Remak–Schmidt–Azumaya).** If a persistence module over `ℝ`
is a direct sum of interval modules in two ways, `⊕_{i ∈ ι} k_{I i} ≅ ⊕_{j ∈ κ} k_{J j}`, then
there is a bijection `σ : ι ≃ κ` with `J (σ i) = I i` for all `i`: the multiset of intervals is
an isomorphism invariant (Chazal, de Silva, Glisse and Oudot, *The structure and stability of
persistence modules*, arXiv:1207.3674, Thm. 1.3, from Azumaya's theorem). -/
theorem_wanted intervalModule_decomposition_unique {ι κ : Type u} (I : ι → Set ℝ)
    (J : κ → Set ℝ) (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected)
    (hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected)
    (e : (∐ fun i => intervalModule k (I i) (hI i).2) ≅
      ∐ fun j => intervalModule k (J j) (hJ j).2) :
    ∃ σ : ι ≃ κ, ∀ i, J (σ i) = I i

/-- **Algebraic stability theorem.** Let `U, V : ℝ ⥤ ModuleCat k` be pointwise
finite-dimensional, with barcodes `I` and `J` (interval decompositions `U ≅ ⊕ k_{I i}` and
`V ≅ ⊕ k_{J j}`). If `U` and `V` are `δ`-interleaved, then for every `δ' > δ` there is a
`δ'`-matching between their barcodes; that is, the bottleneck distance of the persistence
diagrams is at most the interleaving distance (Chazal, de Silva, Glisse and Oudot,
arXiv:1207.3674, Thm. 4.11, the stability inequality `d_i ≥ d_b`, stated there for q-tame
modules, which include the pointwise finite-dimensional ones; the source attributes the
stability theorem to Cohen-Steiner, Edelsbrunner and Harer, *Stability of persistence diagrams*,
DCG 37 (2007), and to Chazal, Cohen-Steiner, Glisse, Guibas and Oudot, *Proximity of
persistence modules and their diagrams*, SoCG 2009). -/
theorem_wanted isMatching_of_interleaving {U V : ℝ ⥤ ModuleCat.{u} k}
    (hU : ∀ t, FiniteDimensional k (U.obj t)) (hV : ∀ t, FiniteDimensional k (V.obj t))
    {ι κ : Type u} {I : ι → Set ℝ} {J : κ → Set ℝ}
    (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected)
    (hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected)
    (eU : U ≅ ∐ fun i => intervalModule k (I i) (hI i).2)
    (eV : V ≅ ∐ fun j => intervalModule k (J j) (hJ j).2)
    {δ : ℝ} (e : Interleaving U V δ) {δ' : ℝ} (hδ' : δ < δ') :
    IsMatching I J δ'

end MathlibExt.Topology.PersistenceModuleWanted
