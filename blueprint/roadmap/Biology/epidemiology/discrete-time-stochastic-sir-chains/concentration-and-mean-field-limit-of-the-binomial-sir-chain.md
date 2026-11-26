# Concentration and mean-field limit of the binomial SIR chain

**Model.** A closed population of size $N=S_t^h+I_t^h+R_t^h$ evolves on the time grid $t\in h\mathbb{N}$. Given the state, each susceptible is infected during $[t,t+h)$ independently with probability $1-e^{-\lambda I_t^h h}$, and each infective recovers with probability $1-e^{-\gamma h}$:

$$I_{t+h}^h=I_t^h+\sum_{i=1}^{S_t^h}X_i-\sum_{i=1}^{I_t^h}Y_i,\qquad S_{t+h}^h=S_t^h-\sum_{i=1}^{S_t^h}X_i,$$

with $X_i\sim\mathrm{Bernoulli}(1-e^{-\lambda I_t^hh})$ and $Y_i\sim\mathrm{Bernoulli}(1-e^{-\gamma h})$. The contact rate $\lambda=\lambda(N)$ may depend on $N$.

**Theorems.**
1. *(Concentration.)* If $0\le\lambda(N)\le\lambda'/N$, there is $K>0$ independent of $N$ such that for every $n$ and $\varepsilon>0$

$$\mathbb{P}\Bigl(\Bigl|\tfrac{I_{nh}^h}{N}-\mathbb{E}\tfrac{I_{nh}^h}{N}\Bigr|>\varepsilon\Bigr)\le e^{-\frac{\varepsilon^2\sqrt N}{2(n+1)K^n}}+n\,e^{-2\sqrt N/K^n},$$

and similarly for $S_{nh}^h/N$.
2. *(Mean-field limit.)* If moreover $N\lambda(N)$ converges and $S_0/N$, $I_0/N$ converge to positive limits, then $\mathbb{E}(S_t/N)$ and $\mathbb{E}(I_t/N)$ converge for every $t\in h\mathbb{N}$, and $S_t/N$, $I_t/N$ converge in probability to these limits.
3. *(Variance.)* For $h\le\min(1,1/\gamma)$, $\operatorname{Var}(R_t^h/N)\le\frac{\gamma t}{N}+\frac{2\gamma^2t^2}{\sqrt N}+th$, which vanishes as $N\to\infty$ and $h\to0$.
4. *(Continuum limit.)* As $h\to0$ the limiting fractions $s(t),i(t)$ are differentiable and solve the SIR system $i'=\lambda si-\gamma i$, $s'=-\lambda si$ (with $\lambda$ the limit of $N\lambda(N)$). For a network of subpopulations with migration, the limits solve $\tilde s'=-\lambda\tilde s\tilde i-\epsilon\Delta^T\tilde s$, $\tilde i'=\lambda\tilde s\tilde i-\gamma\tilde i-\epsilon\Delta^T\tilde i$, with $\Delta$ the graph Laplacian.

## Expansion

Conditionally on the current state, the expected next state is a linear map of $(I,S)$ given by the matrix $\begin{pmatrix}e^{-\gamma h}&1-e^{-\lambda I h}\\0&e^{-\lambda Ih}\end{pmatrix}$, so multiplying by inverses of these matrices along the path produces a martingale. Martingale concentration bounds for its increments, together with $\lambda\le\lambda'/N$, give concentration at rate $\sqrt N$ with constants growing geometrically in the number of steps. Concentration turns the stochastic recursion into a deterministic one in the limit, and expanding $1-e^{-\lambda Ih}=\lambda Ih+O(h^2)$, with conditional covariances of order $h^2$, recovers the SIR differential equations as $h\to0$.

## Sources

- F. Protin, J. Martel, D. T. Nguyen, H. T. T. Nguyen, "Unified modelling of epidemics by coupled dynamics via Monte-Carlo Markov Chain algorithms", arXiv:2106.13463 (2021), Section on the abstract model (binomial transitions and martingale lemma), conditions on $\lambda(N)$, Theorems 2–3, Corollaries 1–2, Propositions 1–4 (numbered in the paper's second theorem series), <https://doi.org/10.48550/arXiv.2106.13463>.
