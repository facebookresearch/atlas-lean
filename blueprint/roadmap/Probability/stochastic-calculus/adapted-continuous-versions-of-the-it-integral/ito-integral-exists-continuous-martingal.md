# A progressive continuous martingale version of the Itô integral

Let $B$ be a real Brownian motion on $(\Omega,\mathcal A,P)$, adapted to a filtration $(\mathcal F_t)_{t\ge0}$. Suppose that $B_t-B_s$ is independent of $\mathcal F_s$ for every $0\le s\le t$, and that every $P$-null set belongs to every $\mathcal F_t$.

Let $H$ be progressively measurable and locally square integrable in time and probability:

$$\forall t\ge0,\qquad \mathbb E\int_{(0,t]}|H_s|^2\,ds<\infty.$$

There exists a real process $J$ which is an $\mathcal F_t$-martingale, is progressively measurable, has continuous paths for every sample, and satisfies, for every fixed $t\ge0$,

$$J_t=\int_0^t H_s\,dB_s\qquad P\text{-almost surely}.$$

The right-hand side is the selected $L^2$ Itô integral. Equality is asserted separately at each fixed time; the selected integral itself is not assumed to have continuous paths or to be indistinguishable from $J$. Any two continuous versions are indistinguishable. Brownian path continuity is only needed almost surely, as in the Brownian-motion hypothesis. Right-continuity of the filtration is not assumed.

Take a continuous modification of the Itô integral. Completeness of the filtration transfers adaptedness across fixed-time almost-sure equality; the adapted modification is a martingale, and adaptedness plus continuous paths gives progressiveness. The complete-filtration convention is stated in Le Gall, [Brownian Motion, Martingales, and Stochastic Calculus](https://link.springer.com/book/10.1007/978-3-319-31089-3), Definition 8.1; the underlying Itô construction follows Karatzas–Shreve, Section 3.2. No necessity of completeness or solution of the SDE existence problem is claimed here.
