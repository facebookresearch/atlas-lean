# Stationary Poisson-relabeling model of local ancestry

Fix a recombination-exposure parameter $T>0$ per Morgan and
$\alpha\in[0,1]$. On the whole real line take a stationary homogeneous
Poisson point process of intensity $T$. Label the intervals between
successive points independently Bernoulli$(\alpha)$, independently of
those points, and let $I_x$ be the label at position $x$ (using the interval
to the right at an endpoint). Label $1$ is ancestry $A$.
The Poisson points are **candidate relabeling points**, not necessarily
ancestry changes: adjacent labels can agree.

Equivalently, this is a stationary two-state Markov chain in the spatial
coordinate, with $0\to1$ rate $\alpha T$ and $1\to0$ rate $(1-\alpha)T$.
The stationary initial label is Bernoulli$(\alpha)$; at $\alpha=0$ or $1$
the ancestry process is constant almost surely.

## Depends on

- [Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md)

## Background

- [Discrete-generation pulse ancestry covariance](allele-cov-ancestry-pulse.md)

## Expansion

For any $x,y\in\mathbb R$, the probability of no candidate point between
them is $e^{-T|x-y|}$. On that event the two labels coincide; otherwise
the endpoint labels are independent. Therefore

$$\mathbb E I_x=\alpha,\qquad
 \operatorname{Cov}(I_x,I_y)=\alpha(1-\alpha)e^{-T|x-y|}.$$

The two-state rates follow by retaining a candidate point only when its
new label differs from the current one. This is an explicit spatial
idealization, not an exact consequence of finite Wright–Fisher evolution.
In the discrete random-mating recursion the covariance after an integer
$n\ge0$ generations is $\alpha(1-\alpha)(1-r)^n$ for recombination
fraction $r$. Relating that expression to the spatial exponential needs
a recombination map and a time convention.
In Gravel's somatic-sampling convention the candidate-point exposure is
$t-1$ for a pulse $t$ generations ago, so here $T=t-1$, not automatically
$t$. This definition uses $T$ as exposure and does not erase that offset.

## Sources

- S. Gravel, *Population genetics models of local ancestry*, Genetics 191 (2012), 607–619, <https://doi.org/10.1534/genetics.112.139808>, <https://arxiv.org/abs/1202.4811>, Model 2, Figure 3(a), and the discussion preceding equation (1), pp. 10–11 of arXiv v2. The labeling construction and covariance calculation are explicit above.
