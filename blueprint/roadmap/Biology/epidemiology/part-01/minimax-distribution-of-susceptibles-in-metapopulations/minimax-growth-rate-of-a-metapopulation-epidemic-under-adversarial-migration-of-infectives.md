# Minimax growth rate of a metapopulation epidemic under adversarial migration of infectives

**Model.** A closed population of size $N$ is divided into $m$ groups. Susceptibles move between groups by an irreducible Markov process with rate matrix $R$ and stationary distribution $\pi$ ($\pi R = 0$, $\pi\mathbf{1} = 1$). Infectives move with an irreducible rate matrix $Q$. Within group $i$, pairs meet at rate $\beta_i/N$ (density-dependent contacts), and infectives recover at rate $\gamma_i$. For large $N$, with susceptibles at equilibrium, the infectives $(Y_1, \dots, Y_m)$ follow a multitype branching process with transitions

$$
Y \to Y + e_i - e_j \text{ at rate } Q_{ji}Y_j, \qquad Y \to Y + e_i \text{ at rate } \beta_i\pi_iY_i, \qquad Y \to Y - e_i \text{ at rate } \gamma_iY_i.
$$

The process depends on $R$ only through $\pi$. Its mean matrix semigroup has generator

$$
A(\pi, Q) = \mathrm{diag}(\beta)\mathrm{diag}(\pi) - \mathrm{diag}(\gamma) + Q,
$$

and the expected number of infectives grows like $e^{\tau(\pi,Q)t}$, where $\tau(\pi, Q)$ is the dominant (Perron) eigenvalue of $A(\pi, Q)$. Let $\mathcal{S}$ be the relative interior of the probability simplex and $\mathcal{Q}$ the set of irreducible rate matrices.

**Theorem.** Let

$$
\chi(\beta,\gamma) = \Big(1 - \sum_{j=1}^m\frac{\gamma_j}{\beta_j}\Big)\Big(\sum_{j=1}^m\frac{1}{\beta_j}\Big)^{-1}, \qquad \pi_i^* = \frac{\gamma_i + \chi(\beta,\gamma)}{\beta_i}.
$$

1. If $\gamma_i > -\chi(\beta,\gamma)$ for all $i$, then $\pi^* \in \mathcal{S}$ and there is $Q^* \in \mathcal{Q}$ with

$$
\tau(\pi, Q^*) \ge \tau(\pi^*, Q^*) = \tau(\pi^*, Q) = \chi(\beta,\gamma) \quad \text{for all } \pi \in \mathcal{S},\ Q \in \mathcal{Q}.
$$

So $(\pi^*, Q^*)$ is a saddle point, and distributing susceptibles by $\pi^*$ caps the growth rate at $\chi(\beta,\gamma)$ whatever the infectives do. One choice is $Q^*_{ij} = \beta_j^{-1}$ for $i \neq j$.
2. If $\chi(\beta,\gamma) < 0$, then $\inf_{\pi\in\mathcal{S}}\sup_{Q\in\mathcal{Q}}\tau(\pi, Q) < 0$: some distribution of susceptibles makes the expected epidemic decline under every migration pattern of the infectives.

The condition in item 1 holds automatically when recovery rates are equal across groups, in which case $\chi = (\sum_j\beta_j^{-1})^{-1} - \gamma$. The optimal $\pi^*$ can be imposed by admission controls at group borders that satisfy detailed balance, without identifying who is infected.

## Depends on

- [Branching-process approximation of early epidemics](../../branching-process-approximation-of-early-epidemi/README.md)

## Expansion

With $\pi = \pi^*$, every row of $\mathrm{diag}(\beta)\mathrm{diag}(\pi^*) - \mathrm{diag}(\gamma)$ equals $\chi$. Hence $A(\pi^*, Q)\mathbf{1} = \chi\mathbf{1}$ for every $Q$, and since $\mathbf{1}$ is a positive eigenvector, $\tau(\pi^*, Q) = \chi$. For fixed $Q$, $\tau(\cdot, Q)$ is strictly convex on $\mathcal{S}$ (Friedland's convexity theorem for the dominant eigenvalue in the diagonal), with partial derivatives $\partial\tau/\partial\pi_i = \beta_iw_iv_i/(w^{T}v)$, where $w$ and $v$ are the left and right Perron vectors. At $\pi^*$ the right vector is $\mathbf{1}$. Choosing $Q^*$ with left Perron vector $w_i \propto \beta_i^{-1}$ makes the directional derivative $\sum_i\beta_iw_i(\pi_i - \pi_i^*) \propto \sum_i(\pi_i - \pi_i^*) = 0$, so $\pi^*$ minimises $\tau(\cdot, Q^*)$. For item 2 use $\tilde\pi_i \propto \gamma_i/\beta_i$: each row of $A(\tilde\pi, Q)\mathbf{1}$ is $\gamma_i\big((\sum_j\gamma_j/\beta_j)^{-1} - 1\big) < 0$, so the Perron eigenvalue is negative.

## Sources

- R. McVinish, P. K. Pollett and A. Shausan, "Limiting the spread of disease through altered migration patterns", arXiv:1508.00293 (2015), Section 2 (branching-process model and saddle-point formulation), Section 2.1 (Theorem 2.1, Corollary 2.2), <https://doi.org/10.48550/arXiv.1508.00293>. Published version: Journal of Theoretical Biology 393 (2016), 60–66, <https://doi.org/10.1016/j.jtbi.2015.12.019>; locators above refer to the arXiv version.
