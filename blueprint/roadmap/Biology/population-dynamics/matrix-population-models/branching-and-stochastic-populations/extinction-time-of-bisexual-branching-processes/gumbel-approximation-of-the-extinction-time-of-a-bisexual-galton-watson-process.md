# Gumbel approximation of the extinction time of a bisexual Galton–Watson process

**Model.** A *mating function* is a map $L:[0,\infty)^2\to[0,\infty)$ with $L(x,y)=0$ unless $x>0$ and $y>0$, $L(x,y)\in\mathbb N$ for $x,y\in\mathbb N$, $L(x,y)\le xy$, and $L$ nondecreasing in each argument (for example $\min\{x,y\}$, $xy$, $x$). Fix a sequence $(L_k)_{k\ge0}$ of mating functions. Generation $0$ has $F_0$ females and $M_0$ males, forming $Z_0$ mating units. Unit $j$ of generation $n$ produces $f_{j,n}$ daughters and $m_{j,n}$ sons; the $f_{j,n}$ are i.i.d., the $m_{j,n}$ are i.i.d., the two families are independent, and the laws do not depend on $j$ or $n$. Then $F_{n+1}=\sum_{j\le Z_n}f_{j,n}$, $M_{n+1}=\sum_{j\le Z_n}m_{j,n}$ (empty sums are $0$), and these form

$$Z_{n+1}=L_{Z_n}(F_{n+1},M_{n+1})$$

mating units: the mating function is indexed by the current number of mating units, not by the generation (the size-dependent model of the source's Section 1.2, whose proofs condition on $Z_n=k$ and apply $L_k$). Let $\tau=\min\{k:Z_k=0\}$, $r_k=\frac1k\mathbb E[Z_{n+1}\mid Z_n=k]$ (which does not depend on $n$), and $p_f=\mathbb P(f_{1,0}=0)$, $p_m=\mathbb P(m_{1,0}=0)$. If every $L_k$ is superadditive, $r=\lim_kr_k=\sup_kr_k$ exists and extinction is certain iff $r\le1$.

**Hypotheses.** $p_m,p_f\in(0,1)$; each $L_k$ is superadditive; there are constants $C,D>0$ with $L_k(x,y)\le Cx$ for all $k$ or $L_k(x,y)\le Dy$ for all $k$; $r<1$ (subcritical); and $p_mp_f<\frac12$, i.e. $\theta:=-\ln(p_mp_f)>\ln2$.

**Results.**

- For every non-trivial process, $\tau$ is unbounded: its right endpoint is $+\infty$.
- If $r<1$, the law of $\tau$, being integer-valued, belongs to no max-domain of attraction of an extreme value distribution.
- Under the hypotheses, with $F_\tau$ the distribution function of $\tau$ (so $F_\tau^m$ is that of the maximum of $m$ independent copies), for all $k\ge1$

$$\exp\{-e^{-\theta k}\} \le \liminf_{m\to\infty} F_\tau^m(k+1+m).$$

  The source's Theorem 1, (8), also prints the upper bound $\limsup_{m\to\infty} F_\tau^m(k+1+m) \le \exp\{-e^{-\theta(k+1)}\}$, which cannot hold: its Proposition 2 gives $\mathbb P(\tau>t\mid Z_0=j)\le jr^t$, so $F_\tau^m(k+1+m)\ge1-mjr^{k+1+m}\to1$. Since $\tau$ is unbounded, $F_\tau(k)^m \to 0$ for every fixed $k$, which is why the argument is shifted by $m$.
- $\tau=\lceil X\rceil$ for a continuous random variable $X$ in the Gumbel domain of attraction, with $\mathbb P(\tau>k)=1-F_X(k)$ (the source's Proposition 3 prints $\lfloor X\rfloor$, but its proof, $\mathbb P[\tau=k]=F_X(k)-F_X(k-1)$, is that of the ceiling), so by the Pickands–Balkema–de Haan theorem the excesses of $X$ over a high threshold are approximately exponential, and $\mathbb P(\tau>k)$ for large $k$ can be estimated by a peaks-over-threshold fit.

## Expansion

Extinction in one generation requires that no daughters or no sons are born, and each mating unit independently produces no offspring of both sexes with probability $p_mp_f=e^{-\theta}$; the proof controls the extinction-time tail through the quantity $\Lambda(k)=p_m^{-Z_k}+p_f^{-Z_k}-1$ built from these probabilities, together with subcriticality $r<1$. The resulting light, essentially exponential tail places the continuous interpolation of $\tau$ in the Gumbel domain, while the integer lattice prevents the discrete law itself from having a non-degenerate limit. In practice one fits a generalized Pareto law to simulated or observed extinction times above a threshold.

## Sources

- E. M. Martín-González, C. Galván-Galván, E. Calvo-Martínez, "How Fast Does Extinction Occur in Bisexual Populations With Size-Dependent Mating Dynamics?", *Methodology and Computing in Applied Probability* 27(4) (2025), 75, Section 2 (model, Hypothesis 1), Propositions 1–3, Theorems 1–3, <https://doi.org/10.1007/s11009-025-10203-4> (preprint arXiv:2501.14879).
