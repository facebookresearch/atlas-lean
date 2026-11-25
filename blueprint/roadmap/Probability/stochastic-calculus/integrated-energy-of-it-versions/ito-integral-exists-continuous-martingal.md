# A continuous Itô version with locally finite integrated energy

Let $B$ be a real Brownian motion on $(\Omega,\mathcal A,P)$, adapted to $(\mathcal F_t)_{t\ge0}$, with $B_t-B_s$ independent of $\mathcal F_s$ whenever $s\le t$. Suppose every $P$-null set belongs to every $\mathcal F_t$. Let $H$ be progressively measurable and satisfy

$$e_T(H)=\mathbb E\int_{(0,T]}|H_s|^2\,ds<\infty\qquad\text{for every }T\ge0.$$

There is one real process $J$ on all nonnegative times which is a martingale for the same filtration, is progressive, has continuous paths for every sample, and satisfies

$$J_t=\int_0^t H_s\,dB_s\quad\text{almost surely for each fixed }t,$$

as well as

$$e_T(J)<\infty,\qquad e_T(J)\le T e_T(H)\quad\text{for every }T\ge0.$$

The construction first selects the existing adapted continuous martingale version. Its progressiveness supplies joint measurability, so the integrated-energy estimate applies to this same version on every horizon. No separate, potentially inconsistent versions are chosen for different horizons.

Right continuity of the filtration and every-sample continuity of the Brownian motion are not required. Completeness is an explicit sufficient hypothesis for selecting the adapted continuous version; this result does not assert its necessity. The conclusion is closure of the progressive finite-energy class under stochastic integration, as needed for Picard iteration, not an SDE existence theorem.
