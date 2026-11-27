# Polynomial calculus degree lower bound for Tseitin formulas

Let $G_n$ be an $r$-regular graph on $n$ vertices with vertex expansion $\varepsilon > 0$ (every set $S$ with $|S| \le n/2$ has $|N(S)| \ge (1+\varepsilon)|S|$), with a charge $\chi$ of odd total, and let $\mathbb{K}$ be a field of characteristic other than $2$. Write the Tseitin parity system in the $\pm 1$ encoding $y_e = 1 - 2x_e$, as the binomials $\prod_{e \ni v} y_e - (-1)^{\chi(v)}$ with the axioms $y_e^2 - 1$. Then this system has no PC refutation of degree $d < \varepsilon n/8$, and hence no Nullstellensatz refutation of such degree. Since the substitution is linear and each vertex constraint involves only $r$ variables, the clause polynomials of $T(G_n,\chi)$ with the Boolean axioms also need PC degree $\Omega(\varepsilon n)$ for fixed $r$.

## Proof sketch

In the $\pm 1$ basis every input is a binomial. On signed multilinear monomials of degree at most $d$ set $\pm m_1 \equiv_d \pm m_2$ when the edges of $m_1 m_2$ (exponents mod $2$) form exactly the edge boundary $E(S)$ of a vertex set $S$ with $|S| < n/2$ whose charge matches the signs. Since $|E(S)| \ge \varepsilon |S|$ for $|S| \le n/2$, this is an equivalence relation for $d < \varepsilon n/8$. The span of the binomials $t - c\,t'$ with $t \equiv_d t'$ is a degree-$d$ pseudo-ideal containing the inputs, closed under multiplication by variables within degree $d$, and it does not contain $1$, so the invariant method applies.

## Depends on

- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)
- [Nullstellensatz proofs and degree](nullstellensatz-proofs.md)
- [Parity systems and bounded-width derivations](../sum-of-squares-proofs/parity-systems-and-bounded-width-derivations.md)

## Proof depends on

- [The invariant method for polynomial calculus degree lower bounds](invariant-method-for-pc-degree.md)
- [Polynomial calculus simulates Nullstellensatz, and conversely without bounds](polynomial-calculus-simulates-nullstellensatz.md)

## Sources

- S. Buss, D. Grigoriev, R. Impagliazzo and T. Pitassi, "Linear Gaps between Degrees for the Polynomial Calculus Modulo Distinct Primes", Journal of Computer and System Sciences 62(2), 267–289, 2001: Section 6, Theorem 8 (with Theorem 4 and Lemmas 10–12).
- D. Grigoriev, "Tseitin's Tautologies and Lower Bounds for Nullstellensatz Proofs", Proceedings of the 39th IEEE Symposium on Foundations of Computer Science (FOCS), 1998: Theorem 1 (the Nullstellensatz case, characteristic other than $2$).
