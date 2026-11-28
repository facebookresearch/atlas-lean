# Weak error of tau-leaping, midpoint and weak trapezoidal methods

**Setting.** A stochastic reaction network (or other population process) with reactions $k=1,\dots,R$, propensities $\lambda_k$ and reaction vectors $\zeta_k$ is written, after normalizing abundances by powers of a large parameter $N$, in the scaled random-time-change form

$$X^N(t)=X^N(0)+\sum_{k=1}^RY_k\Big(N^\gamma\int_0^tN^{c_k}\lambda_k(X^N(s))\,ds\Big)\zeta^N_k,$$

with $Y_k$ independent unit Poisson processes, $|\zeta^N_k|=N^{-m_k}$, $c_k\le m_k$, and $X^N$, $\lambda_k$ of order one; $\gamma$ is the natural time scale and $N^\gamma\sum_kN^{c_k}$ the cost of one exact path. The approximations are, with step $h$: **Euler tau-leaping** (fire $\mathrm{Poisson}(\lambda'_k(Z)h)$ reactions of each type with propensities frozen at the start of the step); the **midpoint method** (take a deterministic half step $y^*=Z+\tfrac h2\sum_k\lambda'_k(Z)\zeta_k$, then leap with propensities at $y^*$); and the **weak trapezoidal method** (a Poisson leap of length $\theta h$ to a $\theta$-midpoint, followed by a leap with intensities $[\alpha_1\lambda'_k(y^*)-\alpha_2\lambda'_k(Z)]^+(1-\theta)h$, $\alpha_1=\frac1{2\theta(1-\theta)}$, $\alpha_2=\frac{(1-\theta)^2+\theta^2}{2\theta(1-\theta)}$). Error is measured in the operator norm $\|\cdot\|^{\nabla^N}_{j\to0}$ built from the scaled difference operators $\nabla^N_kf(x)=N^{c_k}(f(x+\zeta^N_k)-f(x))$.

**Theorem (global weak error).** Let $h<N^{-\gamma}$, $T=nh$, $P_{\cdot,h}$ the one-step operators and $\mathcal P_t$ the exact semigroup. Then

$$\|P^n_{E,h}-\mathcal P_{nh}\|^{\nabla^N}_{2\to0}=O\big(N^{2\gamma}h\,e^{C_2N^\gamma T}\big),$$

$$\|P^n_{M,h}-\mathcal P_{nh}\|^{\nabla^N}_{3\to0}=O\big([N^{3\gamma}h^2+N^{2\gamma-\min_km_k}h]\,e^{C_3N^\gamma T}\big),$$

$$\|P^n_{\mathcal T,h}-\mathcal P_{nh}\|^{\nabla^N}_{3\to0}=O\big(N^{3\gamma}h^2\,e^{C_3N^\gamma T}\big),$$

with $C_j=O(\|\lambda\|^{\nabla^N}_j)$ explicit. So Euler tau-leaping is first order, the weak trapezoidal method is second order in $h$ regardless of how $h$ compares with $N$, and the midpoint method is second order only when $h\gg N^{-\gamma-\min_km_k}$ (otherwise its error is first order with a small constant).

## Expansion

A Lax-equivalence-type estimate bounds the global error by $n$ times the local (one-step) error times the growth of the exact semigroup in the $\nabla^N$-norms: $\|P^n_h-\mathcal P_{nh}\|_{m\to0}=O\big(n\|P_h-\mathcal P_h\|_{m\to0}\max_\ell\|\mathcal P_{\ell h}\|_{m\to m}\big)$, and $\|\mathcal P_tf\|^{\nabla^N}_n\le\|f\|^{\nabla^N}_ne^{N^\gamma C_nt}$. Local errors are $O(N^{2\gamma}h^2)$ for Euler, $O(N^{3\gamma}h^3+N^{2\gamma-\min m_k}h^2)$ for the midpoint method, whose deterministic half step ignores the Poisson noise of the first half-step (an error of order the jump size $N^{-m_k}$), and $O(N^{3\gamma}h^3)$ for the weak trapezoidal method, whose two Poisson stages are weighted by $\alpha_1,\alpha_2$ (with $\alpha_1-\alpha_2=1$) so that the second-order terms of the local expansion cancel. Measuring errors in operator norms adapted to the system's scalings, rather than letting $h\to0$ with the system fixed, explains why methods that are formally second order can behave as first order for realistic step sizes in multiscale biochemical networks. The bounds grow like $e^{N^\gamma T}$, so they are informative when $\gamma\le0$.

## Sources

- David F. Anderson and Masanori Koyama, "Weak Error Analysis of Numerical Methods for Stochastic Models of Population Processes", Multiscale Modeling & Simulation 10 (2012), 1493–1524, <https://doi.org/10.1137/110849699>; numbering as in arXiv:1102.2922: Section 1 (scaled model), Section 2.2 (scaled biochemical models), Algorithms 1–3, Theorem 4.1, Theorems 5.5, 5.6, 5.8, 6.1, 6.4, 6.5, 6.7 and Corollary 6.6.
