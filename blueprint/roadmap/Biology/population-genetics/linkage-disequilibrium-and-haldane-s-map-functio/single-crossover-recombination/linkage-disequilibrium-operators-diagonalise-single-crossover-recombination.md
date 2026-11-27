# Linkage disequilibrium operators diagonalise single-crossover recombination

Use the recombinators $R_G$, $G \subseteq L$, and the continuous-time single-crossover recombination equation with crossover rates $\varrho_\alpha > 0$ from the [closed-form solution](closed-form-solution-of-continuous-time-single-crossover-recombination.md). Define the **linkage disequilibrium (LDE) operators**

$$T_G = \sum_{H \supseteq G} (-1)^{|H\setminus G|}\, R_H, \qquad G \subseteq L,$$

which map non-negative measures to signed measures on $X$. By Möbius inversion on the lattice of subsets of $L$, $R_G = \sum_{H \supseteq G} T_H$.

**Theorem (Baake, Theorem 3).** If $\omega_t$ solves the single-crossover recombination equation, then for every $G \subseteq L$

$$\frac{d}{dt}\, T_G(\omega_t) = - \Big( \sum_{\alpha \in L\setminus G} \varrho_\alpha \Big)\, T_G(\omega_t),$$

so $T_G(\omega_t) = \exp\big(-t\sum_{\alpha \notin G}\varrho_\alpha\big)\, T_G(\omega_0)$.

The nonlinear transform $\omega \mapsto (T_G(\omega))_{G\subseteq L}$ turns the coupled nonlinear system into decoupled linear equations with exponential solutions. The components of $T_G(\omega)$ are correlation functions of all orders between the segments defined by $G$; they are built on ordered partitions of the sites, in contrast with the general-partition disequilibria of classical multilocus theory. $T_L(\omega_t)$ is constant (the linkage-equilibrium product), and every other component decays.

## Depends on

- [Closed-form solution of continuous-time single-crossover recombination](closed-form-solution-of-continuous-time-single-crossover-recombination.md)

## Expansion

Insert $\omega_t = \sum_K a_K(t) R_K(\omega_0)$. By the linearity identity, $T_G(\omega_t) = \sum_K a_K(t)\, (T_G R_K)(\omega_0)$, and $T_G R_K = \mathbf 1_{K \subseteq G}\, T_G$: if some $\alpha \in K\setminus G$ exists, the terms $H$ and $H \triangle \{\alpha\}$ of the alternating sum cancel because $R_{H\cup K} = R_{(H\triangle\{\alpha\})\cup K}$. Then $T_G(\omega_t) = \big(\sum_{K\subseteq G} a_K(t)\big) T_G(\omega_0)$, and $\sum_{K \subseteq G} a_K(t)$ is the probability that no link outside $G$ has seen a crossover, namely $\prod_{\alpha \notin G} e^{-\varrho_\alpha t}$.

## Sources

- E. Baake, *Deterministic and stochastic aspects of single-crossover recombination*, in *Proceedings of the International Congress of Mathematicians 2010 (ICM 2010)*, Vol. IV (2011), 3037–3053, <https://doi.org/10.1142/9789814324359_0178>; preprint arXiv:1101.2081, <https://doi.org/10.48550/arXiv.1101.2081>.
