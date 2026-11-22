/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.WronskianComposition

@[expose] public section

open Polynomial

-- Consumer with the original binders.
example {k : Type*} [Field k] [IsAlgClosed k] {u v s t U V : Polynomial k}
    (huv : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree)
    (hw : Polynomial.wronskian u v ≠ 0) (hst : IsCoprime s t)
    (hs : 0 < max s.natDegree t.natDegree) (hw' : Polynomial.wronskian s t ≠ 0)
    (hU : ∀ x : k, v.eval x ≠ 0 →
      U.eval x = v.eval x ^ max s.natDegree t.natDegree * s.eval (u.eval x / v.eval x))
    (hV : ∀ x : k, v.eval x ≠ 0 →
      V.eval x = v.eval x ^ max s.natDegree t.natDegree * t.eval (u.eval x / v.eval x)) :
    IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ Polynomial.wronskian U V ≠ 0 :=
  Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero huv hu hw hst hs hw' hU hV

universe w

-- Higher-universe consumer.
example {k : Type w} [Field k] [IsAlgClosed k] {u v s t U V : Polynomial k}
    (huv : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree)
    (hw : Polynomial.wronskian u v ≠ 0) (hst : IsCoprime s t)
    (hs : 0 < max s.natDegree t.natDegree) (hw' : Polynomial.wronskian s t ≠ 0)
    (hU : ∀ x : k, v.eval x ≠ 0 →
      U.eval x = v.eval x ^ max s.natDegree t.natDegree * s.eval (u.eval x / v.eval x))
    (hV : ∀ x : k, v.eval x ≠ 0 →
      V.eval x = v.eval x ^ max s.natDegree t.natDegree * t.eval (u.eval x / v.eval x)) :
    IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ Polynomial.wronskian U V ≠ 0 :=
  Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero huv hu hw hst hs hw' hU hV
