/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelian images of ultraproducts and products (Kourovka Notebook Problem 20.13)

Kourovka Notebook, Problem 20.13 (G. M. Bergman), marked solved in the 21st issue: (a) if an abelian
group can be written as a homomorphic image of a nonprincipal countable ultraproduct of not
necessarily abelian groups `Gᵢ`, must it be a homomorphic image of a nonprincipal countable
ultraproduct of abelian groups? (b) If an abelian group can be written as a homomorphic image of a
direct product of an infinite family of not necessarily abelian finite groups, can it be written as
a homomorphic image of a direct product of finite abelian groups?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.AbelianImagesUltraproducts

/-! # Abelian images of products and ultraproducts

The original import path re-exports both parts of Kourovka Problem 20.13.
-/
