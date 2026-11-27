# Laplace limit of inter-particle distances in an actin-turnover particle system

**Model.** A toy model of actin filament turnover by branching: $N \ge 2$ point particles on $\mathbb{R}$ (projected filament centers). At each time step $n+1$ an ordered pair of distinct indices $(i_{n+1}, j_{n+1})$ is chosen uniformly, independently of the past, together with an independent offset $\Delta_{n+1}$ from a fixed symmetric centered law with variance $\sigma^2$, and

$$X^{n+1}_k = X^n_k \ (k \ne i_{n+1}), \qquad X^{n+1}_{i_{n+1}} = X^n_{j_{n+1}} + \Delta_{n+1}:$$

one filament disassembles and a new one branches off a randomly chosen parent at a random displacement. The cloud forms transient clusters but its center of mass wanders, so one studies positions relative to the mean, rescaled by $\sqrt N$: $\bar X^n_k = (X^n_k - \langle X^n\rangle)/\sqrt N$, and the distances $D^n_{1j} = \bar X^n_1 - \bar X^n_j$. Let $\xi$ be the characteristic function of $\Delta$ and $\lambda_N$ the law of $\Delta/\sqrt N$.

**Theorem (one distance, finite $N$).** As $n \to \infty$, $D^n_{12}$ converges in law to $\mu_N$ with characteristic function

$$\psi_N(s) = \frac{\xi(s/\sqrt N)}{N - 1 - (N-2)\,\xi(s/\sqrt N)}, \qquad s \in \mathbb{R},$$

and for $N > 2$, $\mu_N = \frac{1}{N-2}\sum_{k\ge1}\big(\frac{N-2}{N-1}\big)^k\lambda_N^{*k}$, a geometric mixture of convolution powers. For Gaussian offsets this is an explicit mixture of centered normals with variances $k\sigma^2/N$.

**Corollary (large population).** $\mu_\infty = \lim_{N\to\infty}\mu_N$ is the Laplace law with mean $0$ and variance $\sigma^2$: characteristic function $\frac{2}{2 + \sigma^2 s^2}$, density $\frac{1}{\sqrt2\,\sigma}e^{-\sqrt2|y|/\sigma}$, whatever the offset law.

**Theorem (joint distances and a single particle).** For each $1 \le k < N$ the joint law of $(D_{12}, \dots, D_{1,k+1})$ converges as $n \to \infty$, with characteristic functions $\psi^k_N$ given by an explicit recursion in $k$; the stationary law of one centered particle has characteristic function $\phi_N(s) = \psi^{N-1}_N(s/N, \dots, s/N)$. As $N \to \infty$ the joint limits $\psi^k_\infty$ exist and satisfy

$$\psi^k_\infty(s_1,\dots,s_k) = \frac{2\sum_i \psi^{k-1}_\infty(\ldots\hat s_i\ldots) + \sum_{i\ne j}\psi^{k-1}_\infty(\ldots\hat s_i, s_j + s_i\ldots)}{k(k+1) + \frac{\sigma^2}{2}\big(s_1^2 + \cdots + s_k^2 + (s_1 + \cdots + s_k)^2\big)},$$

with $\psi^1_\infty(s) = 2/(2 + \sigma^2 s^2)$, and the single-particle limit law $\nu_\infty$ exists.

## Expansion

Look backward in time: two particles' positions share a common ancestor, and the distance between them is a sum of independent offsets along the two lineages back to the most recent common ancestor, as in a Moran genealogy. Each step merges the two lineages with probability of order $1/N$ and otherwise adds an offset to one of them with probability of order $1/N$, so the number of offsets separating them is geometric, giving the convolution-power mixture; with offsets scaled by $1/\sqrt N$ the geometric sum of many small steps converges to a Laplace law (a Brownian motion evaluated at an exponential time). The recursion for joint distances is the same coalescent bookkeeping for $k+1$ lineages, which is why the limit resembles a Fleming–Viot superprocess seen from its center.

## Sources

- Cecilia González-Tokman and Dietmar B. Oelz, "Asymptotic limits of transient patterns in a continuous-space interacting particle system", Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences 480 (2024), 20230754, <https://doi.org/10.1098/rspa.2023.0754>; numbering as in arXiv:2409.19175: Section 1 (process), Section 2 (renormalized process), Theorem 3.1, Corollaries 3.2–3.3, Theorem 5.1, Corollary 5.2, Theorems 6.1–6.2.
