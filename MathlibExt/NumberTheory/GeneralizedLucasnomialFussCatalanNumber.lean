/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasPolytopicNumber

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Lucasnomial Fuss–Catalan numbers.** Let $P$ be Lucas parameters, that is, nonzero
reals $p$ and $q$ whose Lucas bracket sequence $U_0 = 0$, $U_1 = 1$, $U_{m+2} = pU_{m+1} + qU_m$
satisfies $U_m \ne 0$ for every $m \ge 1$. Write $U_m! = U_1 U_2 \cdots U_m$, and let the
Lucasnomial coefficient $\binom{m}{k}_U$ be $\frac{U_m!}{U_k! \, U_{m-k}!}$ for $k \le m$ and $0$
for $k > m$. For natural numbers $a$, $r$ and $n$, the generalized Lucasnomial Fuss–Catalan number
of $P$ is the real number

$$C_{U,a,r}(n) = \frac{U_r}{U_{(a-1)n+r}} \binom{an+r-1}{n}_U.$$

The source takes $a \ge 2$, $r \ge 1$ and $n \ge 1$. Here $a$, $r$ and $n$ range over all natural
numbers: $a - 1$ and $an + r - 1$ are truncated at $0$, and the quotient is $0$ when
$U_{(a-1)n+r} = 0$.

Source: Ballot, JIS Vol. 21. Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`; source SHA-256
`ca51d34e717a237b02bca4bfa28c57dfc15c81f1276c7634d5abe998d1c48b89`. -/
noncomputable def generalizedLucasnomialFussCatalan
    (P : LucasParameters) (a r n : ℕ) : ℝ :=
  (lucasBracket P r / lucasBracket P ((a - 1) * n + r)) *
    lucasnomial P (a * n + r - 1) n

/-- **Generalized Lucasnomial Fuss–Catalan numbers in the r, s, t notation.** Let $P$ be Lucas
parameters, that is, nonzero reals $p$ and $q$ whose Lucas bracket sequence $U_0 = 0$, $U_1 = 1$,
$U_{m+2} = pU_{m+1} + qU_m$ satisfies $U_m \ne 0$ for every $m \ge 1$. Write
$U_m! = U_1 U_2 \cdots U_m$, and let the Lucasnomial coefficient $\binom{m}{k}_U$ be
$\frac{U_m!}{U_k! \, U_{m-k}!}$ for $k \le m$ and $0$ for $k > m$. For natural numbers $r$, $s$
and $t$, define the real number

$$C_{U,r,s}(t) = \frac{U_s}{U_{(r-1)t+s}} \binom{rt+s-1}{t}_U.$$

The source takes $r \ge 2$, $s \ge 1$ and $t \ge 1$. Here $r$, $s$ and $t$ range over all natural
numbers: $r - 1$ and $rt + s - 1$ are truncated at $0$, and the quotient is $0$ when
$U_{(r-1)t+s} = 0$.

Source: Ballot, JIS Vol. 24. Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`; source SHA-256
`de2518f50026ac96429ae9113e738d224b1c1b732eec121bd4da5e8d60207f1c`. -/
noncomputable def generalizedLucasnomialFussCatalanRS
    (P : LucasParameters) (r s t : ℕ) : ℝ :=
  (lucasBracket P s / lucasBracket P ((r - 1) * t + s)) *
    lucasnomial P (r * t + s - 1) t

/-- **The two indexings of the generalized Lucasnomial Fuss–Catalan numbers agree.** For all Lucas
parameters $P$, with Lucas bracket sequence $U$, and all natural numbers $a$, $r$ and $n$, the
generalized Lucasnomial Fuss–Catalan number $C_{U,a,r}(n)$ equals $C'_{U,a,r}(n)$, where
$C'_{U,r,s}(t)$ denotes the generalized Lucasnomial Fuss–Catalan number in the r, s, t notation.
The two definitions are the same function.

Source: Ballot, JIS Vol. 21 and Vol. 24. Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`. -/
theorem generalizedLucasnomialFussCatalan_vol24_eq
    (P : LucasParameters) (a r n : ℕ) :
    generalizedLucasnomialFussCatalan P a r n =
      generalizedLucasnomialFussCatalanRS P a r n := rfl

end

end MetaMathlibExt
