# Convergent vectors of a continued fraction

Let $x$ be a rational number with regular
continued fraction $[q_0; q_1, q_2, \dots]$, and let $A_j$ and $B_j$ be the numerators and
denominators of its convergents, given by $A_{-2} = 0$, $A_{-1} = 1$, $B_{-2} = 1$, $B_{-1} = 0$
and $A_j = q_j A_{j-1} + A_{j-2}$, $B_j = q_j B_{j-1} + B_{j-2}$ for $j \ge 0$. Stark's
convergent vectors of $x$ are $v_j = (B_j, A_j)$ for $j \ge -2$, so $v_{-2} = (1, 0)$,
$v_{-1} = (0, 1)$ and $v_j = v_{j-2} + q_j v_{j-1}$ for every $j \ge 0$ for which $q_j$ exists.

If the expansion terminates with $q_m$, then $v_j = v_m$ for all $j > m$; for $j < -2$ the
value is set to $v_0$.

## Sources

- Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10, Section 3 (CF algorithm).
