# Super-polynomial SIRS survival on scale-free random graphs

In the SIRS process on a graph $G$, each vertex is susceptible, infected or recovered. An infected vertex infects each susceptible neighbour at rate $\lambda$ and recovers at rate $1$. A recovered vertex loses immunity and becomes susceptible again at the deimmunization rate $\varrho$. The survival time $T$ is the first time no vertex is infected. On a single star, recovered vertices stop the infection: the expected survival time is polynomial in $n$ whatever $\lambda$ is. This contrasts with the SIS process, which survives super-polynomially long on stars.

**Theorem (scale-free graphs).** Fix constants $\varepsilon>0$ and $\varrho>0$. Let $G$ be a hyperbolic random graph, a geometric inhomogeneous random graph, or a Chung–Lu graph on $n$ vertices with power-law degree exponent $\gamma\in(2,3)$. Consider the SIRS process on $G$ with infection rate

$$
\lambda\in(0,1],\qquad \lambda=\Omega\Big(n^{-\frac{1}{(2+1/\varrho)(\gamma-1)}+\varepsilon}\Big),
$$

started with the highest-degree vertex infected and all others susceptible. Then

$$
\mathbb E[T]=\Omega\big(n^{\ln n}\big).
$$

So SIRS epidemics have a vanishing threshold and survive super-polynomially long on these sparse, non-expanding graphs. Expansion is therefore not necessary for SIRS epidemic behaviour: enough mutually connected large stars suffice.

## Expansion

The proof shows that each model w.h.p. has $\ln(n)^2$ vertices of degree at least $(cn/\ln(n)^2)^{1/(\gamma-1)}$, and that these hubs are joined to each other by short paths, forming connected stars. One star cannot sustain the infection, because its leaves become immune. But while one star's leaves are recovering, the infection can reach a neighbouring star whose leaves have already lost immunity. A gambler's-ruin estimate on the number of currently infected stars then gives the $n^{\ln n}$ lower bound. The term $1/\varrho$ in the exponent reflects how long immunity lasts.

## Sources

- A. Göbel, N. Klodt and M. S. Krejca, "Reemergence of the Epidemic Threshold in SIRS Infections on Connected Stars", arXiv:2605.19835 (2026), Section 4 (corollary on scale-free survival and supporting lemmas). <https://doi.org/10.48550/arXiv.2605.19835>
