# Sums-of-Squares proof system

A degree-$d$ Sums-of-Squares (SoS) derivation of $p \ge c_0$ from real polynomial inequalities over Boolean variables writes $p - c_0$ as a sum of squares plus the hypotheses and Boolean axioms, each multiplied by a sum of squares, with every term of degree at most $d$; a refutation derives $-1 \ge 0$.

Let $\mathcal{P} = \{p_1(x) \ge 0, \dots, p_m(x) \ge 0\}$ with $p_i \in \mathbb{R}[x_1, \dots, x_n]$, and let $\Sigma^2_k$ be the set of polynomials of degree at most $k$ that are sums of squares of polynomials. A **degree-$d$ Sums-of-Squares derivation** of $p(x) \ge c_0$ from $\mathcal{P}$ is an identity

$$
q_0(x) + \sum_{i=1}^{\ell} p_i(x) \, q_i(x) = p(x) - c_0 ,
$$

where $q_0 \in \Sigma^2_d$, each $p_i$ is a member of $\mathcal{P}$ or one of the Boolean axioms $x_j^2 - x_j \ge 0$ and $x_j - x_j^2 \ge 0$, and $q_i \in \Sigma^2_{d - \deg(p_i)}$. A **degree-$d$ SoS refutation** of $\mathcal{P}$ is a degree-$d$ derivation of the constant $-1$. Its **degree** is $\max_i \deg(p_i q_i)$, and its **monomial size** is $\|q_0\| + \sum_i \|p_i q_i\|$, where $\|q\|$ is the number of nonzero monomials of $q$.

An equation $f = 0$ is included as the two inequalities $f \ge 0$ and $-f \ge 0$, so its multiplier is in effect an arbitrary polynomial; in particular the Boolean axioms enter with arbitrary multipliers. On a system of equations with no inequalities, a refutation is an identity $\sum_i g_i f_i + \sum_j h_j (x_j^2 - x_j) + q_0 = -1$ with $g_i, h_j$ arbitrary and $q_0$ a sum of squares.

## Depends on

None.

## Proof depends on

None.

## Sources

- Noah Fleming, Pravesh Kothari, Toniann Pitassi, "Semialgebraic proofs and efficient algorithm design", *Foundations and Trends in Theoretical Computer Science* 14(1-2), 2019, https://doi.org/10.1561/0400000086; numbering of ECCC report TR19-106, revision 3, 2020 (Definitions 3.54 and 3.55 and the complexity measures after them).
- Christoph Berkholz, "The relation between polynomial calculus, Sherali-Adams, and sum-of-squares proofs", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, https://doi.org/10.4230/LIPIcs.STACS.2018.11 (Section 2.2, identity (3)).
