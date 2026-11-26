# Ornstein–Uhlenbeck fluctuations of the ancestral selection graph line count

**Model.** In a Moran model of size $N$ with pair-resampling rate $\gamma/N$ per ordered pair and selective advantage $s_N$, the *line counting process* $B^N$ of the ancestral selection graph counts the potential ancestors of a sample, with transition rates
$$r(k, k+1) = k\,s_N\Big(1 - \frac kN\Big) \quad\text{(branching)}, \qquad r(k, k-1) = \frac{\gamma}{N}\binom k2 \quad\text{(coalescence)}.$$
Its stationary law is Binomial$\big(N, \frac{2s_N}{2s_N + \gamma}\big)$ conditioned to be nonzero, with mean $\mu^B_N = \frac{2s_N}{2s_N+\gamma}N$ and standard deviation $\sigma^B_N = \sqrt{\frac{2s_N}{2s_N+\gamma}\big(1 - \frac{2s_N}{2s_N+\gamma}\big)N}$. Define the rescaled process
$$\widetilde B^N_t = \frac{B^N_{t/s_N} - \mu^B_N}{\sigma^B_N}.$$
Selection is *strong* if $s_N \to s > 0$ and *moderate* if $s_N \to 0$ with $Ns_N \to \infty$.

**Theorem.**
1. *(Moran ASG.)* In the strong or moderate selection regime, if $\widetilde B^N_0 \to \nu$ in distribution, then $\widetilde B^N \to Y$ in distribution in the Skorokhod space $D_{\mathbb R}[0, T]$ for every $T < \infty$, where $Y$ is the Ornstein–Uhlenbeck process
$$dY_t = -Y_t\,dt + \sqrt2\,dW_t, \qquad Y_0 \sim \nu.$$
2. *(Logistic branching processes.)* For a logistic branching process with branching rate $\rho_N$, offspring law $(\pi_k)$ with finite third moment, mean $\bar\pi$ and second moment $v^2$, pairwise competition rate $c_N$ and death rate $d_N$, if $\rho_N \to 0$, $\rho_N/c_N \to \infty$, $c_N/d_N \to \infty$ and a regularity condition on the density-dependence $h_N$ holds, then the centered and scaled process converges to the Ornstein–Uhlenbeck process $dY_t = -\bar\pi Y_t\,dt + \sqrt{v^2 + \bar\pi}\,dW_t$.

## Depends on

- [The ancestral selection graph line count as a non-explosive chain](../diffusion-theory/selection-duality-and-general-one-dimensional-di/realized-asg-line-counting-process-countable-ctm.md)

## Expansion

When selection is not weak the line count is large, of order $Ns_N$, and concentrates around the equilibrium where branching balances coalescence; on the selective time scale $1/s_N$ the drift linearizes around that equilibrium with rate $1$, and the noise from branching and coalescence events contributes variance $2$ after normalization by the binomial standard deviation, giving an OU limit. The proof extends the Ethier–Kurtz functional limit theorem to generators defined on growing state spaces. The OU description quantifies how many potential ancestors must be tracked when computing fixation probabilities and ancestral types under strong selection.

## Sources

- F. Boenkost, A.-L. Weinel, "Ornstein–Uhlenbeck fluctuations for the line counting process of the ancestral selection graph", arXiv:2409.10360 (2024), Definition 2.1, Section 2.3 (rescaling and selection regimes), Theorems 1–2, <https://doi.org/10.48550/arXiv.2409.10360>.
