# Asymptotic enumeration and link CLT for G-saturated secondary structures

**Setting.** A homopolymer secondary structure on $\{1,\dots,n\}$ is a noncrossing set of base pairs (links) $(i,j)$, $i<j$, with no base in two links, such that every hairpin loop contains at least $\theta \ge 0$ unpaired bases and every stem (maximal run of stacked links) satisfies a minimum-length threshold $\tau \ge 0$. With the **base stacking energy** $E(S) = -T(S)$, where $T(S)$ is the sum of the sizes of all stems, a structure is **G-saturated** (locally optimal for the stacking energy) if no valid link can be added that extends an existing stem. A structure is **saturated** (locally optimal for the Nussinov energy, $-1$ per link) if no link can be added at all. For $\tau>0$ the two notions coincide; for $\tau=0$ saturated structures form a strict subclass of G-saturated ones.

**Tree characterization (Lemma 2).** G-saturated structures with at least one link are in bijection with admissible weighted rooted plane trees in which every corner at a leaf has weight at most $\theta+1$ and no two adjacent corners both have strictly positive weight.

**Generating function.** Let $g(t,s)$ count G-saturated structures with at least one link, $t$ marking unpaired bases and $s$ marking links. With $u=t^{\theta}(1+t)$, $v=t/(1-t)$ and $x=s^{\tau+1}/(1-s)$ there is an auxiliary series $f(t,s)$ with

$$
f = Q(t,s,f), \qquad Q = u + 2vxf + \frac{1 + 2vx^2f^2(1+vxf)}{1 - xf - vx^2f^2} - 1 - xf,
$$

$$
g = \frac{xf\,\bigl(1 + 2v + (1+v)vxf\bigr)}{1 - xf - vx^2f^2}.
$$

**Theorem (asymptotics, Proposition 1).** Fix $p>0$ and give each structure weight $p^{\#\text{links}}$; let $g_p(t)$ be the weighted generating function by sequence length ($g_p(t) = g(t,pt^2) + t/(1-t)$ for G-saturated structures). For all thresholds $\theta,\tau$ there are computable constants $c>0$ and $\gamma>0$ with

$$
[t^n]\,g_p(t) \sim c\,\gamma^n\,n^{-3/2}, \qquad n \to \infty .
$$

For G-saturated structures $\gamma>1$. The same asymptotic form holds for all secondary structures, again with $\gamma>1$, and for saturated structures with $\gamma>0$ (the source proves $\gamma>1$ only for general and G-saturated structures). Taking $p=3/8$ makes $[t^n]g_{3/8}(t)$ the expected number of such structures on a uniformly random sequence in $\{A,C,G,U\}^n$ (weight $4$ per free base, $6$ allowed labelings out of $16$ per pair).

**Theorem (number of links, Proposition 2).** Let $X_n$ be the number of links of a G-saturated (or saturated, or general) structure of length $n$ drawn with probability proportional to $p^{\#\text{links}}$. There are computable $\mu,\sigma>0$ such that $(X_n - \mu n)/(\sigma\sqrt n)$ converges in distribution to a standard normal law.

## Expansion

The plane-tree encoding turns the local optimality constraints into local conditions on corner weights, so the class is specified by a one-line algebraic equation $f=Q(t,s,f)$ with $Q$ rational with nonnegative coefficients. The Drmota–Lalley–Woods theorem (Theorem 3 of the source) then gives a square-root singularity at the unique $(t_0,y_0)$ solving $y=\Phi(t,y)$, $\Phi_y(t,y)=1$, hence $c\gamma^n n^{-3/2}$ with $\gamma = 1/t_0$; aperiodicity follows from explicit single-edge trees contributing to every length $n \ge 2\tau+\theta+3$, and $\gamma>1$ because $Q$ involves $1/(1-t)$, forcing $t_0<1$. Structures with no link contribute only $t/(1-t)$, which is negligible. The central limit law follows from Drmota's bivariate version (Theorem 4 of the source), applied with $u$ marking links.

## Depends on

- [RNA secondary structure](../../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)

## Sources

- É. Fusy and P. Clote, "Combinatorics of locally optimal RNA secondary structures", arXiv:1112.4610 (2011), Sections 4.4 (Lemma 2 and the system for G-saturated structures) and 5 (Theorems 3–4, Propositions 1–2), <https://doi.org/10.48550/arXiv.1112.4610>.
