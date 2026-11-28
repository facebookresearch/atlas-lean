# Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings

Let $(E,r)$ be a metric space and $T>0$. Let $D([0,T],E)$ be the set of càdlàg paths $x:[0,T]\to E$ (right-continuous on $[0,T)$, with left limits on $(0,T]$) and $\Lambda_T$ the set of increasing homeomorphisms $\lambda$ of $[0,T]$. The J1 metric is

$$d(x,y)=\inf_{\lambda\in\Lambda_T}\max\Bigl(\sup_{t\in[0,T]}|\lambda(t)-t|,\ \sup_{t\in[0,T]}r\bigl(x(t),y(\lambda(t))\bigr)\Bigr).$$

Then:

- the inclusion $C([0,T],E)\to D([0,T],E)$, with the uniform metric on $C([0,T],E)$, is $1$-Lipschitz and a topological embedding;
- for each $t\in[0,T]$ the evaluation $\pi_t(x)=x(t)$ is Borel measurable, and $\pi_t$ is continuous at every $x$ that is continuous at $t$ (in particular $\pi_0$ and $\pi_T$ are continuous).

For $E=\mathbb R$ with $r(a,b)=|a-b|$ this is the [Skorokhod space of real paths](skorokhod-space-d-0-t-with-j1-metric.md).

## Depends on

- [Skorokhod space D[0,T] with J1 metric](skorokhod-space-d-0-t-with-j1-metric.md)

## Proof depends on

- [Pointwise limits of measurable functions are measurable](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable-of-tendsto-metrizable.md)

## Expansion

A full page must establish that $d$ is a metric, the $1$-Lipschitz inclusion and the fact that J1 convergence to a continuous path is uniform convergence (which gives the embedding), continuity of $\pi_t$ at paths continuous at $t$, and Borel measurability of $\pi_t$, for instance by writing $f\circ\pi_t$, for bounded Lipschitz $f$, as a limit of the J1-continuous maps $x\mapsto\varepsilon^{-1}\int_t^{t+\varepsilon}f(x(s))\,ds$ (for $t<T$).

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), <https://en.wikipedia.org/wiki/Convergence_of_Probability_Measures> (book description), Chapter 3 (the Skorokhod topology).
