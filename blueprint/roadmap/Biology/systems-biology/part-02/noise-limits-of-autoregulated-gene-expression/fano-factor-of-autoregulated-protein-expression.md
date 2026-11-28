# Fano factor of autoregulated protein expression

**Model.** A gene switches between an off and an on state, transcribes mRNA when on, mRNA is translated into protein, and mRNA and protein decay. Under negative (positive) autoregulation the switching-off (switching-on) rate is proportional to the current amount of protein. With system size $N$, protein density $V^N_P = X_P/N$ and gene and mRNA dynamics fast compared with protein dynamics, stochastic averaging over the fast variables gives:

- *Law of large numbers.* If the initial densities converge, $V^N_P \Rightarrow v_P$, the solution of $\dot v_P = F(v_P)$, where $F(v) = \kappa_3\, \mathbb E_{\pi_v}[V_R] - \nu_3 v$ is translation (at rate $\kappa_3$ times the mRNA level averaged over the quasi-stationary distribution $\pi_v$ of the fast subsystem, which depends on $v$ through feedback) minus protein decay at rate $\nu_3$; the equilibrium $v_P^*$ solves $F(v_P^*) = 0$.
- *Central limit theorem.* $\sqrt N\,(V^N_P - v_P) \Rightarrow U$, where

    $$U(t) = U(0) + \int_0^t c\big(v_P(s)\big)\,dW(s) + \int_0^t F'\big(v_P(s)\big)\,U(s)\,ds,$$

    with a standard Brownian motion $W$ and an effective diffusion coefficient $c$ that includes the fluctuations of the averaged fast gene and mRNA processes.

**Equilibrium Fano factor.** In equilibrium $U$ is an Ornstein–Uhlenbeck process with variance $c(v_P^*)^2 / \big(-2F'(v_P^*)\big)$, so the protein Fano factor is

$$\frac{\mathbb V[X_P]}{\mathbb E[X_P]} \approx \frac{\mathbb V[U]}{v_P^*} = -\frac{c(v_P^*)^2}{2\,F'(v_P^*)\, v_P^*},$$

independent of $N$.

**Limits of noise.** Compared with the unregulated gene with the same mean protein level, negative feedback makes $F'(v_P^*)$ more negative and reduces the Fano factor, but under the abundant-protein scaling ($X_P = O(N)$) by at most a factor of $2$: the Fano factor is at least $1/2$ (Eq. 14), approached under strong repression when mRNA noise is negligible. These results assume abundant protein; for small amounts of protein under strong repression the source shows that the Fano factor can become arbitrarily small. Positive feedback flattens $F$ at the equilibrium ($F'(v_P^*) \to 0^-$), so the Fano factor is potentially unbounded.

## Expansion

For the linear SDE $dU = F'(v^*)U\,dt + c(v^*)\,dW$ with $F'(v^*) < 0$, Itô's formula for $U^2$ gives $\frac{d}{dt}\mathbb E[U^2] = 2F'(v^*)\mathbb E[U^2] + c(v^*)^2$, whose fixed point is the stationary variance above. Multiplying by $N$ converts the density variance to molecule numbers and $N v^*_P$ is the mean, which produces the dimensionless ratio. Feedback enters through $F'$: negative feedback adds a restoring term to the protein decay, positive feedback subtracts one; it also changes $c$ through the gene-switching noise, and balancing the two effects yields the factor-two bound for repression. The formula exchanges the limits $t \to \infty$ and $N \to \infty$; stochastic simulations agree closely and improve on earlier linear-noise approximations.

## Sources

- P. Czuppon, P. Pfaffelhuber, "Limits of noise for autoregulated gene expression", Journal of Mathematical Biology 77 (2018) 1153–1191, Section 3 (Theorem 1, law of large numbers, Eqs. 4–5; Theorem 2, central limit theorem, Eqs. 8–9; Fano factor, Eqs. 10–14; comparison with earlier negative-feedback results, Eq. 24) and Appendix C (equilibrium covariance of two-dimensional Ornstein–Uhlenbeck processes, Corollary 1), <https://doi.org/10.1007/s00285-018-1248-4> (PMC6153675).
