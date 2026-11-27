# Strong error bound for jump-diffusion approximation of multiscale reaction networks

**Multiscale model.** A reaction network with reactions $k = 1, \dots, R$ and species abundances of different orders is rescaled by a large parameter $N$: species $i$ is measured in units $N^{\alpha_i}$, reaction $k$ has rate of order $N^{\rho_k}$ with $\rho_k = \gamma + \beta_k + \nu_k^-\cdot\alpha$, and has rescaled stoichiometric vector $\nu^N_{ki} = \nu_{ki}/N^{\alpha_i}$. In the random time-change representation, with independent unit Poisson processes $\xi_k$,

$$X^N(t) = X^N(0) + \sum_{k=1}^R \xi_k\Big(N^{\rho_k}\int_0^t\lambda_k(X^N(s))\,ds\Big)\nu^N_k.$$

**Jump-diffusion approximation.** Replace the Poisson process of a fast reaction (say $k = 1$) by its mean plus a Brownian fluctuation, keeping the slow reactions discrete:

$$Z^N(t) = X^N(0) + N^{\rho_1}\!\int_0^t\lambda_1(Z^N(s))\,ds\,\nu^N_1 + W_1\Big(N^{\rho_1}\!\int_0^t\lambda_1(Z^N(s))\,ds\Big)\nu^N_1 + \sum_{k>1}\xi_k\Big(N^{\rho_k}\!\int_0^t\lambda_k(Z^N(s))\,ds\Big)\nu^N_k,$$

where $W_1$ is a standard Brownian motion independent of $\xi_k$, $k > 1$, constructed from $\xi_1$ by the Komlós–Major–Tusnády coupling.

**Theorem.** Assume the propensities $\lambda_k$ are Lipschitz (constants $L_k$) and bounded ($\sup_x\lambda_k \le \bar\lambda_k$), and $|\nu^N_1| = O(N^{-m_1})$ with $N^{-m_1} \asymp \sum_{i\in\mathcal{R}_1}N^{-\alpha_i}$ over the species changed by reaction $1$. Then

$$\sup_{t\le T}\mathbb{E}\,|X^N(t) - Z^N(t)| \le C_N\Big(C'\frac{\log N^{\rho_1}}{N^{m_1}} + \frac{K''}{N^{2\rho_1 + m_1}}\Big),$$

where $C_N$ does not depend on which reaction is approximated by a diffusion. The KMT coupling satisfies $\sup_t|\tilde\xi_1(t) - W_1(t)|/\log(2\vee t) < \infty$ a.s. for the centred process $\tilde\xi_1(t) = \xi_1(t) - t$, with exponential tail bounds on $[0, \delta n]$.

## Proof sketch

Writing $\xi_1(u) = u + \tilde\xi_1(u)$ and coupling $\tilde\xi_1$ with $W_1$ at distance $O(\log u)$, the difference $X^N - Z^N$ is driven by the coupling error at internal time $N^{\rho_1}\!\int\lambda_1$, of size $\log N^{\rho_1}$, multiplied by the jump size $N^{-m_1}$, plus Lipschitz propagation terms controlled by Gronwall and the optional-sampling identity $\mathbb{E}|\xi(\sigma_1) - \xi(\sigma_2)| = \mathbb{E}|\sigma_1 - \sigma_2|$ for stopping times. Since the bound is explicit in $(\rho_k, m_k)$, it is evaluated for every reaction to decide which reactions can be simulated by an SDE (small bound: fast reactions changing abundant species) and which must remain discrete, yielding an adaptive partitioning algorithm for hybrid simulation.

## Sources

- Arnab Ganguly, Derya Altintan and Heinz Koeppl, "Jump-Diffusion Approximation of Stochastic Reaction Dynamics: Error Bounds and Algorithms", *Multiscale Modeling & Simulation* 13 (2015), 1390–1419, <https://doi.org/10.1137/140983471>. Preprint version: arXiv:1409.4303 (2014), Section 5 (model setup, Poisson optional-sampling and KMT coupling lemmas, error-bound theorem), <https://doi.org/10.48550/arXiv.1409.4303>.
