# Gumbel approximation of the extinction time of a bisexual Galton–Watson process

**Model.** Generation $n$ has $F_n$ females and $M_n$ males, which form $Z_n=L_n(F_n,M_n)$ mating units through mating functions $L_n$ (for example $\min\{x,y\}$, $xy$, $x$). Unit $j$ produces $f_{j,n}$ daughters and $m_{j,n}$ sons, identically distributed across $j,n$, and $F_{n+1}=\sum_{j\le Z_n}f_{j,n}$, $M_{n+1}=\sum_{j\le Z_n}m_{j,n}$. Let $\tau=\min\{k:Z_k=0\}$, $r_k=\frac1k\mathbb E[Z_{n+1}\mid Z_n=k]$, and $p_f=\mathbb P(f_{1,0}=0)$, $p_m=\mathbb P(m_{1,0}=0)$. If every $L_n$ is superadditive, $r=\lim_kr_k=\sup_kr_k$ exists and extinction is certain iff $r\le1$.

**Hypotheses.** $p_m,p_f\in(0,1)$; each $L_n$ is superadditive; there are constants $C,D>0$ with $L_n(x,y)\le Cx$ for all $n$ or $L_n(x,y)\le Dy$ for all $n$; $r<1$ (subcritical); and $p_mp_f<\frac12$, i.e. $\theta:=-\ln(p_mp_f)>\ln2$.

**Results.**

- For every non-trivial process, $\tau$ is unbounded: its right endpoint is $+\infty$.
- If $r<1$, the law of $\tau$, being integer-valued, belongs to no max-domain of attraction of an extreme value distribution.
- Under the hypotheses, the maxima of independent copies of $\tau$ are asymptotically squeezed between the Gumbel laws $\exp\{-e^{-\theta k}\}$ and $\exp\{-e^{-\theta(k+1)}\}$, for all $k\ge1$.
- Consequently $\tau=\lfloor X\rfloor$ for a continuous random variable $X$ in the Gumbel domain of attraction, with $\mathbb P(\tau>k)=1-F_X(k)$, so by the Pickands–Balkema–de Haan theorem the excesses of $X$ over a high threshold are approximately exponential, and $\mathbb P(\tau>k)$ for large $k$ can be estimated by a peaks-over-threshold fit.

## Expansion

Extinction in one generation requires that no daughters or no sons are born, and each mating unit independently produces no offspring of both sexes with probability $p_mp_f=e^{-\theta}$; the proof controls the extinction-time tail through the quantity $\Lambda(k)=p_m^{-Z_k}+p_f^{-Z_k}-1$ built from these probabilities, together with subcriticality $r<1$. The resulting light, essentially exponential tail places the continuous interpolation of $\tau$ in the Gumbel domain, while the integer lattice prevents the discrete law itself from having a non-degenerate limit, which is why the Gumbel bounds differ by one unit of $k$. In practice one fits a generalized Pareto law to simulated or observed extinction times above a threshold.

## Sources

- E. M. Martín-González, C. Galván-Galván, E. Calvo-Martínez, "How Fast Does Extinction Occur in Bisexual Populations With Size-Dependent Mating Dynamics?", *Methodology and Computing in Applied Probability* 27(4) (2025), 75, Section 2 (model, Hypothesis 1), Propositions 1–3, Theorems 1–3, <https://doi.org/10.1007/s11009-025-10203-4> (preprint arXiv:2501.14879).
