# Reproduction-event site frequency spectrum of a supercritical birth-death process

Let $(N_t)$ be a linear birth-death process started from one individual, with birth rate $\lambda$ and death rate $\mu<\lambda$, and net growth rate $r=\lambda-\mu$. At each birth the child acquires a Poisson$(\nu)$ number of new mutations. Run the process to time $T$, condition on $N_T\ge n$, and sample $n$ individuals uniformly. Let $R^k_{n,T}$ be the number of birth events whose child has exactly $k$ descendants in the sample, $R^{\ge2}_{n,T}=\sum_{k\ge2}R^k_{n,T}$, and let $M^k_{n,T}$, $M^{\ge2}_{n,T}$ be the corresponding numbers of mutations (the site frequency spectrum); given the $R$'s, the $M^k_{n,T}$ are independent Poisson$(\nu R^k_{n,T})$.

1. If $ne^{-rT_n}\to 0$, then for every fixed $k\ge 2$

$$\frac{R^k_{n,T_n}}{n}\xrightarrow{P}\frac{\lambda}{r\,k(k-1)},\qquad \frac{M^k_{n,T_n}}{n}\xrightarrow{P}\frac{\lambda\nu}{r\,k(k-1)}.$$

2. If $n^{3/2}(\log n)\,e^{-rT_n}\to 0$, then

$$\frac{1}{\sqrt n}\Big(R^{\ge2}_{n,T_n}-\frac{n\lambda}{r}\Big)\Rightarrow\mathcal N\Big(0,\frac{\lambda^2}{r^2}\Big),\qquad \frac{1}{\sqrt n}\Big(M^{\ge2}_{n,T_n}-\frac{n\lambda\nu}{r}\Big)\Rightarrow\mathcal N\Big(0,\frac{\lambda^2\nu^2}{r^2}+\frac{\lambda\nu}{r}\Big).$$

Compared with mutations at constant rate along branches, where the total length of branches supporting $k$ leaves is asymptotically $n/(r\,k(k-1))$, mutations tied to birth events keep the $1/(k(k-1))$ shape of the spectrum but scale it by the birth rate $\lambda$, even though the intensity of birth events observed along an ancestral lineage is time-inhomogeneous.

## Expansion

The coalescent tree of the sample is a coalescent point process: draw the sampling probability $Y_{n,T}$ with density $n\delta_T y^{n-1}/(y+\delta_T-y\delta_T)^{n+1}$, $\delta_T=r/(\lambda e^{rT}-\mu)$, then i.i.d. node depths $H_1,\dots,H_{n-1}$ with an explicit density given $Y_{n,T}$. Birth events along a branch whose descendants are not sampled are thinned by the probability of leaving no sampled descendant, which makes the intensity of observed births along a lineage time-dependent. When $ne^{-rT}\to 0$, $Y_{n,T}\approx n\delta_T/W$ with $W$ exponential, and the node depths can be coupled to i.i.d. limits with summable error, so $R^k$ becomes a sum of nearly independent contributions; a law of large numbers and, under the stronger time condition, a central limit theorem follow from moment computations.

## Sources

- Yubo Shuai, "Transition in the ancestral reproduction rate and its implications for the site frequency spectrum", arXiv:2402.16306 (2024), Proposition 1.1, Theorems 1.2 and 1.3, Corollaries 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2402.16306>
