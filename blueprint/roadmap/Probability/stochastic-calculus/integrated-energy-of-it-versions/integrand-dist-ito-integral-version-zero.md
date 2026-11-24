# Integrated energy of a jointly measurable Itô version

Let $B$ have real Brownian finite-dimensional laws, be adapted to a filtration $(\mathcal F_t)_{t\ge0}$, and have increments $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$. Let $H$ be progressively measurable and write

$$e_T(H)=\mathbb E\int_{(0,T]}|H_s|^2\,ds.$$

Fix $T\ge0$ and suppose $e_T(H)<\infty$. Let $J$ be a jointly measurable real process such that for every fixed $t\in[0,T]$,

$$J_t=\int_0^t H_s\,dB_s\qquad\text{almost surely},$$

where the right side is the existing actual Itô integral. Then

$$e_T(J)\le T e_T(H).$$

Only version equality on the chosen horizon is needed. No continuity, adaptedness of $J$, or completeness of the filtration is assumed. Joint measurability is formulated on real time through $J_{\max(s,0)}$.

The proof uses Tonelli to exchange the time and sample integrals, transfers each fixed-time moment across the almost-sure version equality, applies the Itô isometry, and bounds the input energy on each smaller interval by the terminal energy. Finiteness on the smaller intervals is established before invoking the isometry. The factor $T$ is a sufficient bound, not a claim of sharpness.
