# Bounded-degree Lovász-Schrijver refutes linear equations over Z2

Every unsatisfiable system of 3-variable linear equations over $\mathbb{Z}_2$, written as linear inequalities, has a Lovász-Schrijver refutation of degree $6$ and polynomial size; low-degree reasoning with real inequalities can thus simulate Gaussian elimination, which Sherali-Adams and Sums-of-Squares of sublinear degree cannot.

Let $\mathbb{E}$ be an instance of $3\mathrm{LIN}(\mathbb{Z}_2)$ over variables $X_1, \dots, X_n$ with $m$ equations. For an equation $E : a_1 X_1 + \dots + a_n X_n = b$ with $a_i, b \in \mathbb{Z}_2$, let $I = \{i \in [n] : a_i \ne 0\}$, where $|I| = 3$, and let $\mathcal{S}(E)$ be the $2^{|I|-1}$ inequalities

$$
\sum_{i \in T} \bar{X}_i + \sum_{i \in I \setminus T} X_i - 1 \ge 0 \qquad \text{for all } T \subseteq I \text{ with } |T| \equiv 1 - b \pmod 2 ,
$$

which a $\{0,1\}$-assignment satisfies over $\mathbb{Q}$ exactly when it satisfies $E$ over $\mathbb{Z}_2$. Let $\mathcal{S}(\mathbb{E})$ be the union of the $\mathcal{S}(E)$.

**Theorem.** If $\mathbb{E}$ is unsatisfiable, then $\mathcal{S}(\mathbb{E})$ has an LS refutation of degree $6$ and size polynomial in $n$ and $m$.

## Expansion

Write $\mathbb{E}$ as $Ax = b$. Unsatisfiability means that $b$ is not in the column space of $A$ over $\mathbb{Z}_2$, so some sum of equations gives $0 = 1$. The refutation follows this Gaussian elimination, representing each derived parity constraint by inequalities about linear forms and using earlier techniques of Grigoriev, Hirsch and Pasechnik for reasoning about gaps of the form $(-\infty, c] \cup [c+1, +\infty)$ with quadratic inequalities; this keeps the degree bounded by $6$ while the size stays polynomial. The argument extends to $3\mathrm{LIN}(\mathbb{Z}_p)$ for primes $p$. By the CSP gap theorem, Polynomial Calculus over the reals, Sherali-Adams and Sums-of-Squares need linear degree on such systems, so bounded-degree LS is a proof system closed under the standard CSP reductions that goes beyond bounded width.

## Depends on

- [Lovász-Schrijver proof systems LS and LS+](lovasz-schrijver-proof-systems.md)

## Proof depends on

None.

## Sources

- Albert Atserias, Joanna Ochremiak, "Proof complexity meets algebra", *ACM Transactions on Computational Logic* 20(1), 2019, https://doi.org/10.1145/3265985; numbering of arXiv:1711.07320v2 (Theorem 18, Section 7).
