# Horner evaluation with operation count

Let $R$ be a commutative semiring, let
$x \in R$, and let $a_0, \dots, a_{n-1} \in R$ be coefficients listed in ascending order of
degree. Horner evaluation starts with the accumulator $v = 0$ and, for $i = n-1, \dots, 0$
in turn, replaces $v$ by $a_i + x v$, charging two operations (one multiplication and one
addition) for each step. It returns the final accumulator together with the total number of
operations charged, a natural number.
