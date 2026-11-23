/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# Pell--Lucas numbers

Source: K. Kaygisiz and A. Şahin, *Generalized Bivariate Lucas p-Polynomials and Hessenberg
Matrices*, Journal of Integer Sequences 15 (2012),
[`kaygisiz3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL15/Kaygisiz/kaygisiz3.tex).
-/

/-- **Pell–Lucas numbers.** The Pell–Lucas numbers are the natural numbers $Q_n$ defined by
$Q_0 = Q_1 = 2$ and $Q_{n+2} = 2 Q_{n+1} + Q_n$ for every natural number $n$.

They are the specialization $L_{1,n}(2,1)$ of the generalized bivariate Lucas $p$-polynomials
$L_{p,n}(x,y)$ of Kaygisiz and Şahin. -/
public def pellLucas : Nat → Nat
  | 0 => 2
  | 1 => 2
  | n + 2 => 2 * pellLucas (n + 1) + pellLucas n

public theorem pellLucas_zero : pellLucas 0 = 2 := rfl

public theorem pellLucas_one : pellLucas 1 = 2 := rfl

public theorem pellLucas_add_two (n : Nat) :
    pellLucas (n + 2) = 2 * pellLucas (n + 1) + pellLucas n := rfl

end

end MetaMathlibExt
