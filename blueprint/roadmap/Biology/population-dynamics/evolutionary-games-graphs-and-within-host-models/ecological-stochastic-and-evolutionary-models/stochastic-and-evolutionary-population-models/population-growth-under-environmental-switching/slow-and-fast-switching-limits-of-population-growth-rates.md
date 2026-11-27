# Slow and fast environmental switching limits of population growth rates

**Model.** A structured population $x(t) \in \mathbb{R}^d_+$ (stages, patches or physiological states) follows

$$x'(t) = A_{\sigma(\omega t)}\, x(t),$$

where $A_1, \dots, A_N$ are $d \times d$ Metzler matrices (nonnegative off-diagonal entries) with $\sum_i A_i$ irreducible, and the environment $\sigma$ is either *periodic* (period $1$, spending the fraction $\alpha_i$ of each period in state $i$, visiting $1, \dots, N$ in order) or *Markovian* (a continuous-time chain with irreducible rates $\xi_{ij}$ and stationary law $\alpha$, rescaled so that $\max_j \sum_{i \ne j}\xi_{ij} = 1$, with jump matrix $Q$: $q_{ij} = \xi_{ij}$ for $i \ne j$, $q_{ii} = 1 - \sum_{j\ne i} q_{ij}$). The parameter $\omega$ is the switching frequency. The stochastic growth rate is the Lyapunov exponent $\Lambda(\omega) = \lim_t \frac1t \log\|x(t)\|$ ($\Lambda_p$ periodic, $\Lambda_M$ Markovian); in the periodic case $\Lambda_p(\omega) = \omega \log \lambda(M(\omega))$ with monodromy matrix $M(\omega) = e^{\omega^{-1}\alpha_N A_N}\cdots e^{\omega^{-1}\alpha_1 A_1}$. Let $\lambda(A)$ be the spectral abscissa, $\bar A = \sum_i \alpha_i A_i$, and $x_i, y_i$ (resp. $\bar x, \bar y$) the right and left Perron eigenvectors of $A_i$ (resp. $\bar A$), normalized by $y_i^{\mathsf T}x_i = 1$ and $\mathbf 1^{\mathsf T}x_i = 1$.

**Theorem.**

1. *(Slow periodic.)* If all $A_i$ are irreducible, $\Lambda_p(\omega) = \sum_i \alpha_i \lambda(A_i) + c_{sp}\,\omega + o(\omega)$ as $\omega \to 0$, with $c_{sp} = \sum_{i=1}^N \ln(x_i^{\mathsf T} y_{i+1})$ (indices mod $N$).
2. *(Fast periodic.)* $\Lambda_p(\omega) = \lambda(\bar A) + c_{fp}\,\omega^{-1} + o(\omega^{-1})$ as $\omega \to \infty$, with $c_{fp} = \bar y^{\mathsf T}\big(\tfrac12\sum_{i<j}\alpha_i\alpha_j[A_j, A_i]\big)\bar x$; for $N = 2$, $c_{fp} = 0$ and the correction is of order $\omega^{-2}$.
3. *(Slow Markovian.)* If all $A_i$ are irreducible, $\Lambda_M(\omega) = \sum_i \alpha_i \lambda(A_i) + c_{sM}\,\omega + o(\omega)$ with $c_{sM} = \sum_{i,j}\alpha_i q_{ij}\ln(y_j^{\mathsf T}x_i)$.
4. *(Fast Markovian.)* $\Lambda_M(\omega) = \lambda(\bar A) + c_{fM}\,\omega^{-1} + o(\omega^{-1})$ with $c_{fM} = \bar y^{\mathsf T}\big(\sum_{i,j}\alpha_i (Q - I)^{-1}_{ij} A_j(\bar x\bar y^{\mathsf T} - I)A_i\big)\bar x$.
5. *(Metapopulations.)* For patch dynamics $A_\sigma = R_\sigma + L$ with diagonal growth rates $R_\sigma$ not all equal and irreducible dispersal matrix $L$: in the fast limit $c_{fM} > c_{fp} = 0$; in the slow limit, if $L$ is symmetric or $d = 2$, then $c_{sp} \le 0$ and $c_{sM} \le 0$, with equality iff all $x_i$ coincide.

## Expansion

Slow switching lets the population settle into each environment's stable stage distribution $x_i$, so growth averages the $\lambda(A_i)$; at each switch the population must project from $x_i$ onto the new reproductive values $y_j$, costing $\ln(y_j^{\mathsf T}x_i) \le 0$ per switch in the symmetric case, which is why slow fluctuations reduce metapopulation growth. Fast switching averages the matrices instead, and the leading correction comes from commutators (periodic) or from the variance of the environment-specific growth along the averaged eigenvector (Markovian); random fast switching therefore inflates growth when patch growth rates differ, while periodic switching between two states does not at first order.

## Sources

- Pierre Monmarché, Sebastian J. Schreiber and Édouard Strickler, "Impacts of Tempo and Mode of Environmental Fluctuations on Population Growth: Slow- and Fast-Limit Approximations of Lyapunov Exponents for Periodic and Random Environments", Bulletin of Mathematical Biology 87 (2025), 81, <https://doi.org/10.1007/s11538-025-01443-z>; numbering as in arXiv:2408.11179: Lemma 1, Theorem 1, Propositions 1–2 and Theorem 3.
