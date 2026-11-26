# Negative binomial law of phase-structured PCR amplification

**Model.** PCR amplification is a continuous-time pure-birth (Yule) process $X(t)$ on $\{1,2,\dots\}$ in which each molecule duplicates independently at a phase-specific rate: time is split into consecutive phases $I_1, I_2, \dots, I_p$ of lengths $\tau_i = |I_i|$ (for example exponential, linear and plateau phases), and the duplication rate during $I_i$ is $r_i$. Start with $n$ template molecules and let $t \in I_k$.

**Theorem.** The probability generating function of $X(t)$ is

$$G(s) = \mathbb{E}\,s^{X(t)} = \left[\frac{s\,e^{-z}}{1 - s(1 - e^{-z})}\right]^n, \qquad z = r_kt + \sum_{i=1}^{k-1}(r_i - r_k)\tau_i ,$$

so $z$ is the integrated duplication rate up to time $t$. Equivalently

$$\mathbb{P}\bigl(X(t) = x\bigr) = \binom{x-1}{n-1}e^{-nz}\bigl(1 - e^{-z}\bigr)^{x-n}, \qquad x \ge n,$$

a negative binomial law with mean $ne^{z}$ and variance $ne^{z}(e^{z} - 1)$.

**Poisson input.** If the initial template number is Poisson with mean $\lambda$ (as in limiting-dilution or digital assays), the generating function becomes $\exp\bigl(\lambda\,[G_1(s) - 1]\bigr)$ with $G_1$ the single-molecule generating function above, which yields a likelihood for $\lambda$.

## Expansion

A Yule process started from one molecule with constant rate $r$ is geometric at time $t$ with success probability $e^{-rt}$; a time-varying rate only changes the clock, $rt \mapsto \int_0^t r(u)\,du = z$, and $n$ independent lineages give the $n$-fold convolution, a negative binomial. The large variance relative to the mean, $\operatorname{Var}/\mathbb{E}^2 \approx 1/n$, shows why low-copy quantification is intrinsically noisy and why estimates should use the full likelihood rather than threshold-cycle regression alone.

## Sources

- A. M. Degoot, W. Ndifon, "Stochastics of DNA Quantification" (2023), Theorem 1, Corollary 1 and Theorem 2, <https://doi.org/10.48550/arXiv.2301.02149>.
