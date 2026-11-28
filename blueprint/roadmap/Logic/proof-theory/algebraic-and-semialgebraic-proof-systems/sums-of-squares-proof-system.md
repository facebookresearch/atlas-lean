# Sums-of-Squares proof system

A degree-$d$ Sums-of-Squares (SoS) derivation writes $p - c_0$ as a sum of squares plus hypotheses times multipliers, all terms of degree at most $d$: inequalities $p_i \ge 0$ get sum-of-squares multipliers, equations $f_j = 0$ (in the equational form) get arbitrary polynomial multipliers. A refutation derives $-1 \ge 0$.

**Inequalities.** Let $\mathcal{P} = \{p_1(x) \ge 0, \dots, p_m(x) \ge 0\}$ with $p_i \in \mathbb{R}[x_1, \dots, x_n]$, and let $\Sigma^2_k$ be the set of polynomials of degree at most $k$ that are sums of squares of polynomials. A **degree-$d$ Sums-of-Squares derivation** of $p(x) \ge c_0$ from $\mathcal{P}$ is an identity

$$
q_0(x) + \sum_{i=1}^{\ell} p_i(x) \, q_i(x) = p(x) - c_0 ,
$$

where $q_0 \in \Sigma^2_d$, each $p_i$ is a member of $\mathcal{P}$ or one of the Boolean axioms $x_j^2 - x_j \ge 0$ and $x_j - x_j^2 \ge 0$, and $q_i \in \Sigma^2_{d - \deg(p_i)}$. A **degree-$d$ SoS refutation** of $\mathcal{P}$ is a degree-$d$ derivation of the constant $-1$. The **degree** of a derivation is $\max(\deg q_0, \max_i \deg(p_i q_i))$; for a refutation the leading terms of $q_0$ must cancel against the other terms, so this equals $\max_i \deg(p_i q_i)$. Its **monomial size** is $\|q_0\| + \sum_i \|p_i q_i\|$, where $\|q\|$ is the number of nonzero monomials of $q$.

**Equations.** For a system $\mathcal{F} = \{f_1 = 0, \dots, f_m = 0\}$ of real polynomial equations over Boolean variables, a **degree-$d$ SoS refutation** in the equational form is an identity

$$
\sum_{i=1}^{m} g_i(x) \, f_i(x) + \sum_{j=1}^{n} h_j(x) \, (x_j^2 - x_j) = -1 - s(x) ,
$$

where $s$ is a sum of squares and the $g_i, h_j$ are arbitrary polynomials, with $\deg s$, $\deg(g_i f_i)$ and $\deg(h_j (x_j^2 - x_j))$ all at most $d$. Mixed systems combine the two forms, inequalities with sum-of-squares multipliers and equations, including the Boolean axioms, with arbitrary ones.

The two forms differ at a fixed degree budget. Writing $f = 0$ as the inequalities $f \ge 0$ and $-f \ge 0$ gives $f$ the multiplier $q_+ - q_-$ with $q_\pm \in \Sigma^2_{d - \deg f}$, and since sums of squares have even degree this has degree at most $2\lfloor (d - \deg f)/2 \rfloor$: for $f = x_1$ and $d = 2$ the multiplier must be a constant, whereas the equational form allows the term $x_2 \cdot x_1$. A statement about SoS degree on equations names the form it uses.

## Depends on

None.

## Proof depends on

None.

## Sources

- Noah Fleming, Pravesh Kothari, Toniann Pitassi, "Semialgebraic proofs and efficient algorithm design", *Foundations and Trends in Theoretical Computer Science* 14(1-2), 2019, https://doi.org/10.1561/0400000086; numbering of ECCC report TR19-106, revision 3, 2020 (Definitions 3.54 and 3.55 and the complexity measures after them: the inequality form with sum-of-squares multipliers).
- Christoph Berkholz, "The relation between polynomial calculus, Sherali-Adams, and sum-of-squares proofs", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, https://doi.org/10.4230/LIPIcs.STACS.2018.11 (Section 2.2, identity (3): the equational form with arbitrary multipliers).
