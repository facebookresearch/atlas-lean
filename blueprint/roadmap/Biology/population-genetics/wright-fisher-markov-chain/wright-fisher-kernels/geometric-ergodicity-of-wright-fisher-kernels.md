# Geometric ergodicity of Wright–Fisher kernels

**Setting.** For $\delta, p \in [0,1]$ the *Wright–Fisher kernel* $P_{\delta,p}$ on $[0,1]$ acts on bounded measurable $h$ by

$$P_{\delta,p}h(x) = p\,\mathbb E\big[h\big(x + (1-x)\delta U\big)\big] + (1-p)\,\mathbb E\big[h\big(x(1-\delta U)\big)\big], \qquad U \sim \mathrm{Unif}(0,1).$$

It models the type-$0$ fraction $x$ in a population (e.g. pathogens within a host): each step a random fraction $\delta U$ of the population is replaced by clonal offspring of a type-$0$ parent with probability $p$, and of a type-$1$ parent otherwise. In the *non-linear* version the reproduction probability depends on the current state and on its own law: if $Z_n \sim \nu_n$, then $Z_{n+1} \sim P_{\delta, s(Z_n, \nu_n)}(Z_n, \cdot)$ for a map $s : [0,1]\times\mathcal P([0,1]) \to [0,1]$ that is $(L_1,L_2)$-Lipschitz:

$$|s(x,\mu) - s(y,\nu)| \le L_1|x-y| + L_2\,W_1(\mu,\nu),$$

where $W_1$ is the Wasserstein-1 distance.

**Theorem.**
1. For every $\delta \in (0,1]$ and $p \in [0,1]$, $P_{\delta,p}$ has a unique invariant law $\beta_{\delta,p}$, and for every initial law $\mu$,

$$W_1\big(\mu P_{\delta,p}^n, \beta_{\delta,p}\big) \le \left(1 - \tfrac{\delta}{2}\right)^n W_1(\mu, \beta_{\delta,p}).$$

2. If $s$ is $(L_1,L_2)$-Lipschitz with $L_1 + L_2 < 1$, the non-linear chain has a unique invariant law $\eta$ and

$$W_1\big(\mathrm{Law}(Z_n), \eta\big) \le \left(1 - \tfrac{\delta(1 - L_1 - L_2)}{2}\right)^n W_1\big(\mathrm{Law}(Z_0), \eta\big).$$

If $s(x,\mu)$ does not depend on $x$, then $\eta = \beta_{\delta,\bar s}$ where $\bar s$ is the unique solution of $s(0, \beta_{\delta,\bar s}) = \bar s$.

## Expansion

Couple two copies of the chain with the same $U$ and the same coin for the parental type. Both update maps $x \mapsto x + (1-x)\delta U$ and $x \mapsto x(1-\delta U)$ contract distances by the factor $1 - \delta U$, whose mean is $1 - \delta/2$; this gives a $W_1$ contraction and hence the unique invariant law. In the non-linear chain, the coins of the two copies can disagree with probability at most $L_1|x-y| + L_2W_1(\mu,\nu)$, and a disagreement moves the copies by at most $\delta U$, which costs at most $\delta(L_1 + L_2)/2$ of the contraction. Under a diffusive scaling in which $\delta_N \to 0$ and the reproduction bias vanishes at a matching rate, with time sped up by $N$, the chains converge to Wright–Fisher diffusions with drift and, in the non-linear case, to a McKean–Vlasov Wright–Fisher diffusion, with propagation of chaos for the corresponding $M$-host systems.

## Sources

- Fernando Cordero, Christian Jorquera, Héctor Olivero and Leonardo Videla, "Wright–Fisher kernels: From linear to non-linear dynamics, ergodicity and McKean–Vlasov scaling limits", Electron. J. Probab. 31 (2026), 1–49, <https://doi.org/10.1214/26-EJP1511>. Numbering follows the arXiv version, arXiv:2410.13107 (2024): Theorems 2.1, 2.7, 2.9 and 2.10, <https://doi.org/10.48550/arXiv.2410.13107>.
