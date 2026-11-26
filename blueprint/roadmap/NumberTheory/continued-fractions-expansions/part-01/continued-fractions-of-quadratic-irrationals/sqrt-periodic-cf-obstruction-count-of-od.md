# Number of unrealizable parity patterns for $\sqrt{d}$, odd length

Let $l \ge 3$ be odd.
Call a parity pattern $(v_1, \dots, v_{(l-1)/2}) \in (\mathbb{Z}/2)^{(l-1)/2}$ realizable if
there are positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i \le l - 1$
and $a_j \equiv v_j \pmod 2$ for $1 \le j \le (l-1)/2$, a natural number $d$ that is not a
perfect square and a natural number $a_0$ with
$\sqrt{d} = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0}]$. If $A$ is the number of parity
patterns that are not realizable, then $3A = 2^{(l-1)/2} - (-1)^{(l-1)/2}$.

Writing $A_m$ for $A$ when $l = 2m + 1$, this gives $A_1 = A_2 = 1$ and
$A_m = A_{m-1} + 2A_{m-2}$ for $m \ge 3$.

## Sources

- Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 3.
