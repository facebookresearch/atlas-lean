# Sherali-Adams proof system

A Sherali-Adams (SA) derivation certifies $p(x) \ge c_0$ from polynomial inequalities over $\{0,1\}^n$ by a static identity: a nonnegative combination of hypotheses and Boolean axioms, each multiplied by a nonnegative junta $\prod_{j \in S} x_j \prod_{k \in T} (1 - x_k)$, equals $p(x) - c_0$; degree is the maximum degree of these products.

Let $\mathcal{P} = \{p_1(x) \ge 0, \dots, p_m(x) \ge 0\}$ be polynomial inequalities over $\mathbb{R}[x_1, \dots, x_n]$. A **Sherali-Adams derivation** of $p(x) \ge c_0$ from $\mathcal{P}$ is a set of polynomials $q_1, \dots, q_\ell$ such that

$$
\sum_{i \in [\ell]} p_i(x) \, q_i(x) = p(x) - c_0 ,
$$

where each $q_i(x) = c_i \prod_{j \in S_i} x_j \prod_{k \in T_i} (1 - x_k)$ is a nonnegative junta with multisets $S_i, T_i \subseteq [n]$ and $c_i \in \mathbb{R}_{\ge 0}$, and each $p_i$ is the constant $1$, a member of $\mathcal{P}$, or one of $x_j^2 - x_j \ge 0$ and $x_j - x_j^2 \ge 0$. A **Sherali-Adams refutation** of $\mathcal{P}$ is a derivation of the constant $-1$. The **degree** of the derivation is $\max_i \{|S_i| + |T_i| + \deg(p_i)\}$ and its **monomial size** is $\sum_i \| p_i q_i \|$, the number of nonzero monomials. A degree-$d$ nonnegative junta is $J_{S,T}(x) = \prod_{i \in S} x_i \prod_{j \in T} (1 - x_j)$ with $S \cap T = \emptyset$ and $|S \cup T| \le d$.

Basic facts:

1. (Soundness and completeness.) There is a degree-$d$ SA refutation of $\mathcal{P}$ if and only if the degree-$d$ Sherali-Adams relaxation $\mathrm{SA}_d(\mathcal{P})$ is infeasible; level $n + \deg(\mathcal{P})$ equals the integer hull.
2. (Size and degree.) Any SA derivation of size $s$ implies a derivation of degree $O(\sqrt{n \log s} + \deg(\mathcal{P}))$.
3. (Resolution.) Every Resolution refutation of width $w$ and size $s$ yields a degree-$(w+2)$ SA refutation of size $\mathrm{poly}(s)$ of the same CNF.

## Expansion

In the static-identity view of Atserias and Ochremiak, Nullstellensatz, Sherali-Adams and positive semidefinite Sherali-Adams are the subsystems of Polynomial Calculus, Lovász-Schrijver and positive semidefinite Lovász-Schrijver in which all applications of the multiplication rule precede all applications of the addition rule; a degree-$d$ proof of the dynamic system with rank $k$ converts to a static proof of degree $d + k$. Every Nullstellensatz proof over the reals is an SA proof. Duality with the LP hierarchy states that the minimum pseudo-expectation of $p$ over degree-$d$ SA pseudo-expectations equals the largest $c_0$ for which $p \ge c_0$ has a degree-$d$ SA derivation.

## Depends on

None.

## Proof depends on

None.

## Sources

- Noah Fleming, Pravesh Kothari, Toniann Pitassi, "Semialgebraic proofs and efficient algorithm design", *Foundations and Trends in Theoretical Computer Science* 14(1-2), 2019, https://doi.org/10.1561/0400000086 (Definitions 2.7, 2.27 and 2.30, Lemmas 2.31 and 2.33, Theorems 2.34 and 2.35, Corollary 2.26).
- Albert Atserias, Joanna Ochremiak, "Proof complexity meets algebra", *ACM Transactions on Computational Logic* 20(1), 2019, https://doi.org/10.1145/3265985; numbering of arXiv:1711.07320v2 (Section 2.3, static identities).
