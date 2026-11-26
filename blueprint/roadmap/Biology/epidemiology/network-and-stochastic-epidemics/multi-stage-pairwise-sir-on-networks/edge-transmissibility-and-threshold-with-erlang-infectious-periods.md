# Edge transmissibility and epidemic threshold with Erlang infectious periods on networks

**Model.** Consider an SIR epidemic on a network in which every node has degree $n$, transmission occurs across each susceptible–infected edge at rate $\tau$ (per link; in a well-mixed comparison $\tau = \beta/n$), and the infectious period is split into $K \ge 1$ stages $I_1, \dots, I_K$, each left at rate $K\gamma$. The infectious period is therefore Erlang (gamma) distributed with shape $K$ and mean $1/\gamma$,

$$g(x) = \frac{(K\gamma)^K x^{K-1} e^{-K\gamma x}}{(K-1)!}, \qquad x > 0 .$$

**Edge transmissibility.** The probability that infection crosses a given $S$–$I$ edge before the infective recovers is

$$\tilde\tau(K) = 1 - \left(\frac{K\gamma}{\tau + K\gamma}\right)^{K} = 1 - \left(1 + \frac{\tau}{K\gamma}\right)^{-K}.$$

For $K = 1$ this is the classical $\tau/(\tau + \gamma)$. Since $(1 + x/K)^{-K}$ decreases in $K$ for fixed $x > 0$, $\tilde\tau(K)$ increases with $K$ at fixed mean infectious period, and

$$\lim_{K \to \infty} \tilde\tau(K) = 1 - e^{-\tau/\gamma},$$

the transmissibility of a fixed infectious period of length $1/\gamma$.

**Threshold.** For the pairwise (pair-approximation) model with the triple closure $[XSY] \approx \frac{n-1}{n}\frac{[XS][SY]}{[S]}$, linearized at the disease-free state $[S] = N$, $[SS] = nN$, the dominant eigenvalue crosses zero exactly when

$$\mathcal R := (n-1)\,\tilde\tau = 1,$$

so outbreaks grow iff $(n-1)\tilde\tau > 1$. By contrast, in the well-mixed multi-stage model $R_0 = \beta/\gamma$ does not depend on $K$; on the network the threshold depends on the shape of the infectious-period distribution through $\tilde\tau$.

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Given an infectious period $x$, the edge transmits with probability $1 - e^{-\tau x}$; averaging over the Erlang density gives $1 - \int_0^\infty e^{-\tau x} g(x)\,dx = 1 - (K\gamma/(\tau + K\gamma))^K$, the Laplace transform of the Erlang law. In the pairwise model an infected node infected through an edge has $n - 1$ remaining susceptible neighbours, each infected with probability $\tilde\tau$, which explains $\mathcal R = (n-1)\tilde\tau$. Formally, the characteristic polynomial of the linearized $(2K+2)$-dimensional closed pairwise system factors so that $\lambda = 0$ is a root iff $(n-1)\tilde\tau = 1$. Less variable infectious periods (larger $K$) raise transmissibility because Jensen's inequality applied to the convex map $x \mapsto e^{-\tau x}$ favours concentrated durations.

## Sources

- N. Sherborne, K. B. Blyuss, I. Z. Kiss, "Dynamics of multi-stage infections on networks", Bulletin of Mathematical Biology 77 (2015) 1909–1933, Lemma 1 with equations (8)–(10), equation (11) and Appendix 2; well-mixed equation (2), <https://doi.org/10.1007/s11538-015-0109-1>, PMCID: PMC4651987.
