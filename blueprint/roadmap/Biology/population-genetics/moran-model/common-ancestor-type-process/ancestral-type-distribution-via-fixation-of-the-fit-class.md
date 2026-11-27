# Ancestral type distribution via fixation of the fit class in the Moran model

**Model.** A haploid Moran population of fixed size $N$ has types $0$ (fit) and $1$ (unfit). Every individual reproduces neutrally at rate $1$, and type-$0$ individuals additionally reproduce selectively at rate $s_N \ge 0$; the offspring replaces a uniformly chosen individual. Every individual mutates at rate $u_N \ge 0$, the new type being $j$ with probability $\nu_j$ ($\nu_0 + \nu_1 = 1$). The number $Z^N_t$ of fit individuals is a birth–death chain with rates

$$\lambda_k = \tfrac{k(N-k)}{N}(1 + s_N) + (N-k)u_N\nu_0, \qquad \mu_k = \tfrac{k(N-k)}{N} + k u_N\nu_1.$$

At stationarity a unique individual at time $t$ is ancestral to the whole population at some later time (the **common ancestor**). Let $h^N_k$ be the probability that the common ancestor is one of the fit individuals when $Z^N_0 = k$; equivalently, the probability that the offspring of all fit individuals present at time $0$, of whatever type, eventually fixes. Then $h^N_0 = 0$, $h^N_N = 1$, a specific fit individual fixes with probability $h^N_k/k$ and a specific unfit one with probability $(1 - h^N_k)/(N-k)$. Write $h^N_k = k/N + \psi^N_k$, so $\psi^N$ is the part due to selective reproduction.

**Theorem.**

1. (Difference equation.) For $0 < k < N$,

$$(\lambda_k + \mu_k)\,h^N_k = \lambda_k h^N_{k+1} + \mu_k h^N_{k-1} + k u_N\nu_1\,\frac{1 - h^N_{k-1}}{N-k+1} - (N-k)u_N\nu_0\,\frac{h^N_{k+1}}{k+1}.$$

2. (Closed form.) With $\chi^n_\ell = \prod_{i=\ell}^{n}\lambda_i/\mu_i$ and $K = \sum_{n=0}^{N-1}\chi^n_1$ (empty products equal $1$), for $1 \le k \le N-1$,

$$\psi^N_{N-k} = \frac{1}{K}\,\frac{k(N-k)}{\mu_{N-k}}\,\frac{s_N}{N^2}\sum_{\ell=0}^{N-k-1}\ \sum_{n=N-k}^{N-1}(n - \ell)\,\chi^\ell_1\,\chi^n_{N-k+1}.$$

3. (Diffusion limit.) If $N u_N \to \theta \in (0,\infty)$, $N s_N \to \sigma \in [0,\infty)$ and $k_N/N \to x$, then $\psi^N_{k_N} \to \psi(x)$, where $\psi$ is the unique solution of Taylor's boundary value problem

$$x(1-x)\psi''(x) + a(x)\psi'(x) - \Big(\theta\nu_1\frac{x}{1-x} + \theta\nu_0\frac{1-x}{x}\Big)\psi(x) + \sigma x(1-x) = 0, \qquad \psi(0) = \psi(1) = 0,$$

with drift $a(x) = (1-x)\theta\nu_0 - x\theta\nu_1 + \sigma x(1-x)$. Its solution is

$$\psi(x) = \sigma\,x^{-\theta\nu_0}(1-x)^{-\theta\nu_1}e^{-\sigma x}\int_0^x(\tilde x - p)\,p^{\theta\nu_0}(1-p)^{\theta\nu_1}e^{\sigma p}\,dp, \qquad \tilde x = \frac{\mathbb E_{\pi_X}[X^2(1-X)]}{\mathbb E_{\pi_X}[X(1-X)]},$$

where $\pi_X(x) \propto x^{\theta\nu_0 - 1}(1-x)^{\theta\nu_1 - 1}e^{\sigma x}$ is Wright's stationary density. The ancestral type distribution is $\alpha_0 = \int_0^1 (x + \psi(x))\,\pi_X(x)\,dx$, $\alpha_1 = 1 - \alpha_0$; in the neutral case $\sigma = 0$, $\psi \equiv 0$ and $\alpha_0 = \mathbb E_{\pi_X}[X]$.

## Depends on

- [Fixation probability of the Moran process](../moran-fixation.md)

## Expansion

Follow forward in time the descendants, of both types, of the $k$ fit individuals together with the type count. First-step analysis on the next event gives item 1: a neutral birth or death moves $k$ by one while keeping the tagged set; a mutation of a fit individual to type $1$ removes it from the fit count but its descendants stay tagged, and a mutation of an unfit individual to type $0$ adds an untagged fit individual, which explains the two correction terms with the per-individual fixation probabilities. Substituting $h = k/N + \psi$ cancels the neutral part and leaves the source term $\tfrac{k(N-k)}{N^2}s_N$, i.e. $\psi^N$ is carried by selective reproduction events. Reindexing from $k = N$ downwards gives a first-order recursion for $\psi^N_{N-k}$ solved by the product weights $\chi$, which are the birth–death stationary weights. Rescaling the difference equation gives Taylor's ODE, and the closed form gives the limit.

## Sources

- Sandra Kluth, Thiemo Hustedt, Ellen Baake, "The common ancestor process revisited", *Bulletin of Mathematical Biology* 75 (2013), 2003–2027, <https://doi.org/10.1007/s11538-013-9871-0>; preprint arXiv:1305.5939, <https://doi.org/10.48550/arXiv.1305.5939>. Numbering of the arXiv version: Section 2 (model), Section 3 (Taylor's boundary value problem, solution and $\alpha$), Section 4 (difference equation for $h^N$, Lemma 2, Theorem 1), Appendix (Theorem 3).
