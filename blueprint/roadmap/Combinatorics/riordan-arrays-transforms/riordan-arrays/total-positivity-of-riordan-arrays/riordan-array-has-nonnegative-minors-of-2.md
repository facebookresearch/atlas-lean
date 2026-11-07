# A total positivity criterion for Riordan arrays

Let $P, Q, A, Z$ be formal power series
over $\mathbb{R}$ with $P(0) \ne 0$, write $[x^n]F$ for the coefficient of $x^n$ in a power
series $F$, and let $a, b, r, s, t \ge 0$ be real numbers. Suppose that

$$A(x)\,(P(x) - rx) = P(x)^2 + sxP(x) + tx^2$$

and

$$Z(x)\,(P(x)^2 - rxP(x)) =
(P(x)^2 + sxP(x) + tx^2)\,Q(x) + (aP(x) + bx)(P(x) - xQ(x)),$$

and let $R$ be the Riordan array whose $A$-sequence is $([x^n]A)_{n \ge 0}$ and whose
$Z$-sequence is $([x^n]Z)_{n \ge 0}$. Let $J(Q(x), P(x))$ be the coefficient matrix whose row
$n \ge 0$ reads $[x^n]Q, [x^n]P, [x^{n-1}]P, \dots, [x^0]P, 0, 0, \dots$. Call a matrix totally
positive when every minor of it is nonnegative. If $J(Q(x), P(x))$ is totally positive,
$s^2 \ge 4t$ and $as + a\sqrt{s^2 - 4t} \ge 2b$, then $R$ is totally positive.

Since $P(0) \ne 0$, the series $P(x) - rx$ and $P(x)^2 - rxP(x)$ are invertible, so the two
hypotheses say $A = (P^2 + sxP + tx^2)/(P - rx)$ and
$Z = ((P^2 + sxP + tx^2)Q + (aP + bx)(P - xQ))/(P^2 - rxP)$.

## Sources

- Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Theorem 2 (`jis-2025-25.7.5-thm-2`).
