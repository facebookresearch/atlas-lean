# Continued fraction along a Farey path of polynomials

Let $F$ be a field, let
$n \in \mathbb N$, let $u_i, v_i \in F[X]$ for $i \ge 0$, and let $c_i \in F$ for $i \ge 1$.
Suppose that $v_0 = 1$ and that for $1 \le i \le n$ we have $c_i \ne 0$,
$\deg v_{i-1} < \deg v_i$ and $u_i v_{i-1} - u_{i-1} v_i = c_i$. Let $a_0, a_1, \ldots \in F[X]$
satisfy $a_0 = u_0$, $a_1 = c_1^{-1} v_1$, $a_2 = -c_2^{-1} c_1 (u_2 v_0 - u_0 v_2)$ and, for
$3 \le i \le n$,

$$a_i = (-1)^{i+1}c_i^{-1}c_{i-1}(u_i v_{i-2} - u_{i-2} v_i)\prod_{j=1}^{i-2} c_j^{2(-1)^{i-j+1}}.$$

Then $a_i$ is nonconstant for $1 \le i \le n$. Moreover, for every $i \le n$ let
$t_i = \varepsilon_i \prod_{j=1}^{i} c_j^{(-1)^{i-j+1}}$, where $\varepsilon_i = 1$ if
$i \equiv 0, 1 \pmod 4$ and $\varepsilon_i = -1$ if $i \equiv 2, 3 \pmod 4$. Then the numerator
$A_i$ and the denominator $B_i$ of the $i$th convergent of the continued fraction
$[a_0; a_1, \ldots, a_n]$ over $F(X)$ are $A_i = t_i u_i$ and $B_i = t_i v_i$, and this
convergent equals $u_i / v_i$.

The paper's coprimality hypothesis $(u_i, v_i) = 1$ is omitted: it follows from the determinant
condition.

## Sources

- Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen, *An Interpretation of Continued Fractions and Farey Graphs in the Field of Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 6.
