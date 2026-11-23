/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Homomorphic images of axiomatizable classes of groups (Kourovka Notebook Problem 1.68)

Kourovka Notebook, Archive of Solved Problems, Problem 1.68 (A. Tarski; Yu. I. Merzlyakov): let `𝔎`
be a class of groups and `Q𝔎` the class of all homomorphic images of groups from `𝔎`. If `𝔎` is
axiomatizable, does it follow that `Q𝔎` is?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.HomomorphicImagesAxiomatizableKourovka1Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.68 (A.
Tarski; Yu. I. Merzlyakov). UnsolvedMath record UM-00700059 (`KOU-1.68`), dataset
ulamai/UnsolvedMath v1.8.0.

A class of groups is a predicate on groups in `Type`; it is axiomatizable if it is the class of
models of some first-order theory of the language of groups `groupLanguage` (MathlibExt), with the
canonical structures. `Q𝔎` consists of the groups that are images of surjective homomorphisms from
groups in `𝔎`.
-/

/-- The group `G`, with its canonical structure for the first-order language of groups, is a model
of the theory `T`. -/
def IsModel (T : FirstOrder.Language.groupLanguage.Theory) (G : Type) [Group G] : Prop :=
  letI := FirstOrder.Language.groupLanguageStructure G
  FirstOrder.Language.Theory.Model G T

/-- The class `K` of groups is axiomatizable: it is the class of models of some first-order theory
of the language of groups. -/
def IsAxiomatizable (K : ∀ (G : Type) [Group G], Prop) : Prop :=
  ∃ T : FirstOrder.Language.groupLanguage.Theory, ∀ (G : Type) [Group G], K G ↔ IsModel T G

/-- The class `QK` of homomorphic images of groups in `K`. -/
def homomorphicImages (K : ∀ (G : Type) [Group G], Prop) (G : Type) [Group G] : Prop :=
  ∃ (H : Type) (_ : Group H) (f : H →* G), K H ∧ Function.Surjective f

/-- Kourovka 1.68 (A. Tarski): if a class `K` of groups is axiomatizable, so is the class `QK` of
all homomorphic images of groups in `K`. -/
def homomorphicImagesOfAxiomatizableClassAxiomatizable : Prop :=
  ∀ K : ∀ (G : Type) [Group G], Prop, IsAxiomatizable K → IsAxiomatizable (homomorphicImages K)

/--
Resolved false: the Kourovka Archive answers 1.68 "Not always", citing Clare (1975): some
axiomatizable class of groups has a class of homomorphic images that is not axiomatizable. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.68 (A. Tarski; Yu. I.
Merzlyakov); resolution: F. Clare, Algebra Universalis 5 (1975), 120-124, Kourovka Archive, Problem
1.68 (Not always).
-/
public theorem_wanted homomorphicImagesOfAxiomatizableClassAxiomatizable_refuted :
    ¬ homomorphicImagesOfAxiomatizableClassAxiomatizable

end MathlibExt.ModelTheory.HomomorphicImagesAxiomatizableKourovka1Problem68Wanted
