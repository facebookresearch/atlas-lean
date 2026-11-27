# Tanaka's formula for Brownian motion at a fixed level

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. Let $a\in\mathbb R$ and let $\operatorname{sgn}(x)=1$ for $x>0$ and $-1$ for $x\le0$. Define

$$L^a_t=|B_t-a|-|B_0-a|-\int_0^t\operatorname{sgn}(B_s-a)\,dB_s,\qquad t\ge0 .$$

Then, almost surely, $t\mapsto L^a_t$ is continuous and nondecreasing, $L^a_0=0$, and $L^a$ increases only on the set $\{s:B_s=a\}$, in the sense that

$$\int_0^\infty\mathbf 1_{\{B_s\ne a\}}\,dL^a_s=0 .$$

The value of $\operatorname{sgn}(0)$ does not matter, since $\int_0^t\mathbf 1_{\{B_s=a\}}\,ds=0$ almost surely. The occupation-density formula and the joint continuity of $(a,t)\mapsto L^a_t$ are not part of this statement.

## Proof depends on

- [Itô's formula for Itô processes with locally integrable coefficients](ito-formula-for-ito-processes-time-dependent-loc.md)

## Expansion

A full proof page must establish the following.

- Approximation: choose convex $C^2$ functions $f_\varepsilon$ with $f_\varepsilon(x)\to|x-a|$ uniformly, $|f'_\varepsilon|\le1$, $f'_\varepsilon(x)\to\operatorname{sgn}(x-a)$ for $x\ne a$, and $f''_\varepsilon\ge0$ supported in $[a-\varepsilon,a+\varepsilon]$. [Itô's formula for Itô processes](ito-formula-for-ito-processes-time-dependent-loc.md) gives $f_\varepsilon(B_t)-f_\varepsilon(B_0)-\int_0^tf'_\varepsilon(B_s)\,dB_s=\frac12\int_0^tf''_\varepsilon(B_s)\,ds$, which is continuous and nondecreasing in $t$.
- Convergence: $\int_0^tf'_\varepsilon(B)\,dB\to\int_0^t\operatorname{sgn}(B-a)\,dB$ uniformly on compacts in probability, by the isometry and dominated convergence (using that $B$ spends zero time at $a$); monotonicity and continuity pass to the limit along a subsequence.
- Support: on an open time interval on which $B\ne a$, $|x-a|$ is smooth near the path, so Itô's formula gives $dL^a=0$ there; the zero set of $B-a$ is closed, so $dL^a$ charges only $\{s:B_s=a\}$.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren der mathematischen Wissenschaften 293, Springer (1999), <https://link.springer.com/book/10.1007/978-3-662-06400-9>, local times (statement and proof).
