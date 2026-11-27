# Polynomial calculus degree lower bound for Tseitin formulas

Let $G_n$ be an $r$-regular graph on $n$ vertices, $n$ odd, with vertex expansion $\varepsilon > 0$ (every set $S$ of vertices with $|S| \le n/2$ has $|N(S)| \ge (1+\varepsilon)|S|$, where $N(S)$ is the set of vertices adjacent to $S$), and give every vertex charge $1$. Write the Tseitin parity system $\mathrm{TS}_n(2)$ in the $\pm 1$ encoding: one variable $y_e$ per edge, the axioms $y_e^2 - 1$, and for each vertex $v$ with neighbours $j_1, \dots, j_r$ the binomial $1 + y_{\{v,j_1\}} \cdots y_{\{v,j_r\}}$. Then over every field $\mathbb{K}$, for all $d < \varepsilon n/8$ there is no PC refutation of $\mathrm{TS}_n(2)$ of degree $d$. Over a field of characteristic other than $2$ the system is unsatisfiable, so its PC refutations have degree at least $\varepsilon n/8$.

## Proof sketch

In the $\pm 1$ basis every input is a binomial. On signed multilinear monomials of degree at most $d$ set $\pm m_1 \equiv_d \pm m_2$ when the edges of $m_1 m_2$ (exponents mod $2$) form exactly the edge boundary $E(S)$ of a vertex set $S$ with $|S| < n/2$ whose charge matches the signs. Expansion makes this an equivalence relation for $d < \varepsilon n/8$. The span of the binomials $t - c\,t'$ with $t \equiv_d t'$ is a degree-$d$ pseudo-ideal containing the inputs, closed under multiplication by variables within degree $d$, and it does not contain $1$, so the invariant method applies. (Derived, not stated in this form by Buss et al.: since polynomial calculus simulates Nullstellensatz, the system also has no Nullstellensatz refutation of degree below $\varepsilon n/8$, the case Grigoriev proves directly; and since the substitution $y_e = 1 - 2x_e$ is linear and each vertex constraint involves only $r$ variables, the clause polynomials of the Tseitin formula with the Boolean axioms also need PC degree $\Omega(\varepsilon n)$ for fixed $r$, for any charge of odd total.)

## Depends on

- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)
- [Parity systems and bounded-width derivations](../sum-of-squares-proofs/parity-systems-and-bounded-width-derivations.md)

## Proof depends on

- [The invariant method for polynomial calculus degree lower bounds](invariant-method-for-pc-degree.md)
- [Nullstellensatz proofs and degree](nullstellensatz-proofs.md)
- [Polynomial calculus simulates Nullstellensatz, and conversely without bounds](polynomial-calculus-simulates-nullstellensatz.md)

## Sources

- S. Buss, D. Grigoriev, R. Impagliazzo and T. Pitassi, "Linear Gaps between Degrees for the Polynomial Calculus Modulo Distinct Primes", Journal of Computer and System Sciences 62(2), 267–289, 2001: Section 2 (the system $\mathrm{TS}_n(2)$ for an $r$-regular graph with $n$ odd and all charges $1$) and Section 6, Theorem 10 (with Theorem 6 and Proposition 11).
- D. Grigoriev, "Tseitin's Tautologies and Lower Bounds for Nullstellensatz Proofs", Proceedings of the 39th IEEE Symposium on Foundations of Computer Science (FOCS), 1998: Theorem 1 (the Nullstellensatz case, characteristic other than $2$).
