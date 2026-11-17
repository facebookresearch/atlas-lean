/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.NativeConnectionProperties

/-!
# Native wedge and coefficient-extension construction requests

Every arrow is normalized on all original native tensor/exterior
generators. The original form differential and coefficient Leibniz
rule are source inputs. Flatness of higher Gauss--Manin is a separate
proof about the actual computed higher connection.

Sources: Stacks Tags 07HY and 07I0; Scholze, arXiv:1205.3463v2,
Definitions 7.4--7.5 and Theorem 8.8.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace WantedExt.CategoryTheory.NativeConnectionProperties

open _root_.CategoryTheory Opposite
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeConnectionProperties

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}] [HasSheafify J AddCommGrpCat.{1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (K O : Sheaf J CommRingCat.{1}) (k : K ⟶ O) (E Ω : Modules O)

public def_wanted nativeCoefficientWedge : WedgeSource O E Ω

variable (d : ∀ U : Cᵒᵖ, O.obj.obj U →+ Ω.val.obj U)
  (nabla : (restrictK K O k).obj E ⟶ (restrictK K O k).obj (oneForms O E Ω))
  (D : FormDifferentialSource K O k Ω d) (W : WedgeSource O E Ω)

public def_wanted nativeCoefficientExtension (h : IsConnection K O k E Ω d nabla) :
  ExtensionSource K O k E Ω nabla D.sections W

end WantedExt.CategoryTheory.NativeConnectionProperties
