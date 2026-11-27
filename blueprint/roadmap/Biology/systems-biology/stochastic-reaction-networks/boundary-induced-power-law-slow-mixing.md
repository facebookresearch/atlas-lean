# Boundary-induced power-law slow mixing of stochastic reaction networks

**Setting.** Let $X$ be a continuous-time Markov chain on $\mathbb{Z}^d_{\ge0}$ (for instance the copy numbers of $d$ species in a mass-action stochastic reaction network). For $n\in\mathbb{N}$ let $\mathbb{I}_n = \{x\in\mathbb{Z}^d_{\ge0} : x_d = 0,\ \|x\|_\infty = n\}$ be the states where the last species is absent and the others have size $n$, and $\|x\|_{d-1,\infty} = \max_{i\le d-1}|x_i|$. Assume, for constants $0<\theta_1\le\theta_2$ and all large $n$: (i) *dominating cycles*: started in $\mathbb{I}_n$, with probability at least $1-c_1 n^{-\theta_1}$ the next excursion off $\{x_d=0\}$ follows one of a family of paths whose total displacement is zero; (ii) *dominating excursions*: with probability at least $1-c_2n^{-\theta_2}$ it follows either such a cycle or one of finitely many excursions that return to $\{x_d=0\}\setminus\{\mathbf{0}\}$; and (iii) *return times*: from every boundary state the successive return times $\nu_i$ to $\{x_d=0\}$ are almost surely finite and $\mathbb{P}_x(\nu_1\ge t)\ge e^{-\kappa t}$ for a constant $\kappa\in(0,\infty)$. Let $\theta = \min\{1+\theta_1,\theta_2\}$.

**Theorem.** For every $\delta\in(0,1)$ there are $N_\delta$ and $C_\delta>0$ such that for all $n>N_\delta$ and $x\in\mathbb{I}_n$,

$$\inf_{t\in[0,\,C_\delta n^{\theta}]} \mathbb{P}_x\big(\|X(t)\|_{d-1,\infty} > n/2\big) \ge \delta .$$

If moreover each communication class has a unique stationary distribution $\pi_x$ with $\sup_{x\in\mathbb{I}_n}\pi_x(\{\|y\|_{d-1,\infty}>n/2\})\to0$, then the $\delta$-mixing time satisfies $\inf_{x\in\mathbb{I}_n} t^{\delta}_{\mathrm{mix}}(x) \ge C'_\delta\,n^{\theta}$ for all large $n$.

**Example (cyclic networks).** For the two-species network $\emptyset \to \alpha_1A+\beta_1B \to \alpha_2A+\beta_2B \to \cdots \to \alpha_{L-1}A+\beta_{L-1}B \to \emptyset$ ($L\ge2$) with nonnegative increasing integers $\alpha_i,\beta_i$ ($\alpha_0=\beta_0=0$) and arbitrary positive mass-action rate constants, the hypotheses hold and the lower bound applies with $\theta=\theta_1=\min_{2\le i\le L}(\alpha_{i-1}-\alpha_{i-2})$; started from $(n,0)$ the mixing time grows at least like $n^{\theta_1}$ even though the chain is positive recurrent.

## Expansion

While species $d$ is absent, the dynamics can only leave the boundary through rare reactions, and with high probability each excursion is a closed cycle that returns the state to where it started. The large coordinates change only through the rare non-cycle excursions, each of probability $O(n^{-\theta_1})$ or $O(n^{-\theta_2})$, so moving the state a distance of order $n$ requires on the order of $n^{\theta}$ excursions. Until then the chain stays in $\{\|x\|_{d-1,\infty}>n/2\}$, which has vanishing stationary mass, so total variation distance to stationarity stays large.

## Sources

- W.-T. L. Fan, J. Kim, C. Yuan, "Boundary-induced slow mixing for Markov chains and its application to stochastic reaction networks", *SIAM Journal on Applied Dynamical Systems* 25(4) (2026), 2538–2584, Theorem 1, Corollaries 1–2 and Theorem 3, <https://doi.org/10.1137/24m1679896> (preprint arXiv:2407.12166).
