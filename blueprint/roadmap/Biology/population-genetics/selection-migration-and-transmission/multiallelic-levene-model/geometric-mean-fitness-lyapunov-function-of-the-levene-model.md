# Geometric-mean fitness is a Lyapunov function of the Levene model

**Model.** A diploid population occupies $\Gamma$ demes (niches). Zygotes are formed by random mating in a single pool, distributed to the demes, and undergo viability selection there; deme $\alpha$ contributes the fixed fraction $c_\alpha>0$ of the adults that form the next mating pool ($\sum_\alpha c_\alpha=1$). With $I$ alleles $A_1,\dots,A_I$ at frequencies $p=(p_1,\dots,p_I)$ in the simplex $S_I$, viabilities $w_{ij,\alpha}>0$ of $A_iA_j$ in deme $\alpha$, marginal fitnesses $w_{i,\alpha}(p)=\sum_j w_{ij,\alpha}p_j$ and mean fitnesses $\bar w_\alpha(p)=\sum_{i,j}w_{ij,\alpha}p_ip_j$, the allele frequencies evolve by

$$p_i'=p_i\sum_{\alpha}c_\alpha\frac{w_{i,\alpha}(p)}{\bar w_\alpha(p)},\qquad i=1,\dots,I.$$

Define the geometric mean of the deme mean fitnesses and its logarithm

$$\tilde w(p)=\prod_\alpha \bar w_\alpha(p)^{c_\alpha},\qquad F(p)=\ln\tilde w(p)=\sum_\alpha c_\alpha\ln\bar w_\alpha(p).$$

Since $\partial\bar w_\alpha/\partial p_i=2w_{i,\alpha}$, the recursion is the gradient-like map $p_i'=p_i\,\partial_iF(p)\big/\sum_jp_j\,\partial_jF(p)$, and its equilibria are exactly the critical points of $F$ on $S_I$.

**Theorem.**

1. $\Delta\tilde w(p)=\tilde w(p')-\tilde w(p)\ge0$ for every $p\in S_I$, with equality if and only if $p$ is an equilibrium; the same holds for $F$.
2. The set $\Lambda$ of equilibria is globally attracting. If every equilibrium is isolated (a generic condition), every trajectory converges to a single equilibrium, generically a local maximum of $\tilde w$.
3. If $F$ is concave on $S_I$, there is exactly one stable equilibrium (a point or a manifold), it is globally attracting, and an internal equilibrium, if one exists, is the global attractor. $F$ is concave in each of the cases: no dominance in every deme ($w_{ij,\alpha}=v_{i,\alpha}+v_{j,\alpha}$); multiplicative fitnesses in every deme; or, in every deme, a globally attracting internal equilibrium for selection alone.
4. Without dominance, the number of non-neutral demes is a generic upper bound on the number of alleles present at an equilibrium.

In particular the Levene model admits no limit cycles or chaos, and with two alleles a protected polymorphism forces every trajectory to converge to an internal equilibrium.

## Depends on

- [Protected polymorphism in the Levene model](../migration-and-selection/protected-polymorphism-in-the-levene-model.md)

## Expansion

The recursion has the Baum–Eagon form $p_i'\propto p_i\,\partial_i\tilde w$ for the function $\tilde w$, a product of powers of homogeneous quadratic polynomials with non-negative coefficients; an inequality of Baum–Eagon type gives $\tilde w(p')\ge\tilde w(p)$ with equality only at fixed points. LaSalle's invariance principle then makes $\Lambda$ globally attracting, and isolation of equilibria upgrades this to convergence. For concavity, $\ln\bar w_\alpha$ is concave whenever $\bar w_\alpha$ is concave (no dominance gives a linear $\bar w_\alpha$ in the allele "values"; multiplicative fitnesses give $\bar w_\alpha=(\sum_i v_{i,\alpha}p_i)^2$), and a concave $F$ on a convex set has a connected set of maximizers, which must be the unique stable equilibrium. The bound on the number of alleles follows because, without dominance, the internal equilibrium conditions are $\Gamma$ linear constraints on the allele frequencies.

## Sources

- Reinhard Bürger, "A Survey on Migration-Selection Models in Population Genetics", *Discrete and Continuous Dynamical Systems, Series B* 19 (2014), 883–959, <https://doi.org/10.3934/dcdsb.2014.19.883>; preprint arXiv:1309.2576, <https://doi.org/10.48550/arXiv.1309.2576>. Numbering of the journal version: Section 5.1 (Theorem 25, after Li 1955, Cannings 1971 and Nagylaki 1992; Corollary 26; Lemma 27; Theorem 28 and Theorem 29, after Nagylaki and Lou 2001), Section 5.2 (Theorem 32).
