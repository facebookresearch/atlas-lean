# Bursty gene expression: Markov chain to PDMP limit and stationary laws

**Model.** In a cell of size $V$, protein copy number $N(t)$ is degraded at rate $r$ per molecule and produced in bursts: transcription events occur at rate $c(N/V)$, where $c : \mathbb{R}_+ \to \mathbb{R}_+$ is Lipschitz with constant $L_c$ (encoding feedback regulation), and each burst adds a geometric number $m \ge 1$ of proteins with $\mathbb{P}(m) \propto p_V^m q_V$, $p_V + q_V = 1$ (each short-lived mRNA is translated with probability $p_V$ before decaying). The concentration $X_V = N/V$ is then a *generalized density-dependent Markov chain* on $\{n/V\}$ with generator

$$\mathcal A_V f\big(\tfrac nV\big) = rn\Big[f\big(\tfrac{n-1}{V}\big) - f\big(\tfrac nV\big)\Big] + c\big(\tfrac nV\big)\sum_{m\ge1} p_V^m q_V \Big[f\big(\tfrac{n+m}{V}\big) - f\big(\tfrac nV\big)\Big].$$

Assume large bursts, $p_V/q_V = V/\lambda$ with $\lambda > 0$ fixed. The candidate limit is the piecewise-deterministic Markov process $X$ with generator

$$\mathcal A f(x) = -rx f'(x) + c(x)\int_0^\infty \big[f(x+y) - f(x)\big]\lambda e^{-\lambda y}\,dy:$$

deterministic exponential decay interrupted by exponentially distributed concentration jumps.

**Theorem.**
1. *(Functional limit.)* If $X_V(0) \Rightarrow X(0)$, then $X_V \Rightarrow X$ in $D(\mathbb{R}_+, \mathbb{R}_+)$ as $V \to \infty$; the same holds for multi-gene networks with regulated burst rates and general jump kernels, and both processes are the unique nonexplosive solutions of their martingale problems.
2. *(Stationary laws.)* If $r > L_c/\lambda$ and $c(0) > 0$, then $X_V$ has the unique stationary distribution

$$\pi_V\big(\tfrac nV\big) = A_V\,\frac{p_V^n}{n!}\prod_{k=0}^{n-1}\Big(\frac{c(k/V)}{r} + k\Big), \qquad n \ge 0,$$

and $X$ has the unique stationary density $p(x) = A\,x^{-1}\exp\!\big(-\lambda x + \frac1r\int_1^x \frac{c(y)}{y}dy\big)$, $x > 0$, with normalizing constants $A_V, A$. Moreover $\pi_V \Rightarrow \pi$.
3. *(Constant burst rate.)* If $c \equiv c > 0$, $\pi_V$ is negative binomial, $\pi_V(n/V) = \frac{(c/r)_n}{n!}p_V^n(1-p_V)^{c/r}$, and $p$ is the Gamma density $\frac{\lambda^{c/r}}{\Gamma(c/r)}x^{c/r-1}e^{-\lambda x}$.
4. *(Exponential ergodicity.)* For a $d$-dimensional PDMP with drift $F$ and burst kernels $\mu_i$ at rates $c_i(x)$, if $\langle F(x) - F(y), x - y\rangle \le -r|x-y|^2$ with $r > \sum_i L_{c_i}\int|x|\mu_i(dx)$, there is a unique stationary law $\pi$ and $W(\pi_t, \pi) \le W(\pi_0,\pi)\,e^{-\tilde r t}$ in Wasserstein distance, $\tilde r = r - \sum_i L_{c_i}\int x\,\mu_i(dx) > 0$.

## Expansion

With burst sizes of order $V$, a geometric number of copies with mean $V/\lambda$ becomes, after division by $V$, an $\mathrm{Exp}(\lambda)$ jump in concentration, while unit-step degradation becomes the drift $-rx$; generator convergence on a core plus well-posedness gives weak convergence. The one-dimensional chain is a birth-and-death-with-jumps chain whose stationary equation telescopes into a product formula; the PDMP density solves the stationary forward equation, a first-order integro-differential equation whose solution under exponential jumps reduces to the stated integral exponent. Coupling two copies with the same jump times and contracting drift gives the Wasserstein bound; the Lipschitz feedback term must not overcome the decay rate. The Gamma limit is the Friedman–Cai–Xie protein distribution.

## Sources

- Xian Chen and Chen Jia, "Limit theorems for generalized density-dependent Markov chains and bursty stochastic gene regulatory networks", Journal of Mathematical Biology 80 (2019), 959–994, <https://doi.org/10.1007/s00285-019-01445-1>; numbering as in arXiv:1909.00038: Theorems 3.2–3.5, Section 4 (generators of the single-gene model), Theorems 4.1, 4.2, 4.5, Corollary 4.4 and Theorem 5.1.
