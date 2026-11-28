# Malthusian behaviour of a typed branching model of telomere length

**Model.** Individuals carry a type $s \in \mathbb S$ (the gamete mean telomere length, $\mathbb S = [l_{\min}, l_{\max}]$, possibly augmented with other inherited traits) and an age $a \ge 0$. An individual of type $s_0$ and age $a$ reproduces at rate $b(s_0, a)$, where $b$ is bounded, measurable and compactly supported in age, and a child born at parental age $a$ has type drawn from a probability kernel $\gamma_{s_0, a}(ds)$; generations $X_n$ are point measures of (type, birth date). Assume $\mathbb S$ is compact, $b(s, a) > 0$ for all $s$ and all $a \in [b_m, b_M]$ (a common fertile age window), and each $\gamma_{s_0,a_0}$ has a positive density $g_{(s_0,a_0)}(s)$ with respect to a reference measure on $\mathbb S$ that is continuous in $(s_0, s, a_0)$, so that $\gamma$ is a continuous kernel. Let $Z = (Z^{(s)}, Z^{(a)})$ be the auxiliary type–age Markov process that follows a single lineage, and define the Feynman–Kac semigroup

$$\delta_{(s_0, a_0)}R_t = \mathbb E_{(s_0, a_0)}\Bigl[\mathbf 1_{Z_t \in \cdot}\,\exp\Bigl(\int_0^t b(Z_u)\,du\Bigr)\Bigr].$$

**Theorem.** There exist a nonnegative measurable function $\eta$ on $\mathbb S \times \mathbb R_+$, constants $\lambda_0 \in \mathbb R$, $\lambda_1 > 0$, $C > 0$ and a probability measure $\Upsilon$ on $\mathbb S \times \mathbb R_+$ such that for all $t \ge 0$ and all $(s_0, a_0)$,

$$\bigl\|e^{\lambda_0 t}\delta_{(s_0, a_0)}R_t - \eta(s_0, a_0)\,\Upsilon\bigr\|_{TV} \le C e^{-\lambda_1 t}.$$

If $\lambda_0 < 0$, the Malthusian parameter $\alpha = \inf\{\lambda : \nu_\lambda(s, \mathbb S \times \mathbb R_+) < \infty \text{ for some } s\}$ of the branching process equals $-\lambda_0$, so the population is Malthusian with stable type–age profile $\Upsilon$.

## Expansion

Many-to-one formulas express the mean reproduction measures of the Crump–Mode–Jagers process through a single random lineage: the expected number of descendants in a set equals an expectation over the lineage process weighted by $\exp(\int b)$, or by $2^{N_t}$ in a representation via a random exploration of a branch. The exponential convergence is a quasi-stationary-distribution statement for the sub-Markovian semigroup $R$; the common fertile window and the positive density of the type kernel give a Doeblin-type minorization uniformly in the initial condition, which yields the eigenvalue $\lambda_0$, eigenfunction $\eta$ and eigenmeasure $\Upsilon$. The model is used to study how parental age at conception and inheritance shape telomere length across generations.

## Sources

- Athanasios Benetos, Olivier Coudray, Anne Gégout-Petit, Lionel Lenôtre, Simon Toupance and Denis Villemonais, "A branching model for intergenerational telomere length dynamics", Journal of Mathematical Biology 90 (2025), 21, <https://doi.org/10.1007/s00285-025-02185-1>; numbering as in arXiv:2311.09678: Propositions 1–5, Corollary 1 and Theorem 1 (Section 3).
