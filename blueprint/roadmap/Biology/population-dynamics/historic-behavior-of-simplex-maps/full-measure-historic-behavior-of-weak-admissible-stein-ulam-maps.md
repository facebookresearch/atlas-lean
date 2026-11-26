# Full-measure historic behavior of weak admissible Stein–Ulam maps

Let $\Delta^{m-1}=\{x\in\mathbb R^m: x_i\ge 0,\ \sum_i x_i=1\}$ be the simplex of type frequencies (as for Volterra and Lotka–Volterra quadratic stochastic operators of population genetics). A continuous map $K:\Delta^{m-1}\to\Delta^{m-1}$ is a **weak admissible Stein–Ulam type map** if:

- **(W1)** there is $p\in\operatorname{int}\Delta^{m-1}$ with $K(\operatorname{int}\Delta^{m-1})\subset\operatorname{int}\Delta^{m-1}$, $K(\partial\Delta^{m-1})\subset\partial\Delta^{m-1}$ and $\operatorname{Fix}(K)\cap\operatorname{int}\Delta^{m-1}=\{p\}$;
- **(W2)** (multiplicative Lyapunov structure) there are continuous $\varphi:\Delta^{m-1}\to[0,\infty)$ and $\psi:\Delta^{m-1}\to[0,1]$ with $\varphi^{-1}(0)=\partial\Delta^{m-1}$, $\varphi(K(x))=\varphi(x)\psi(x)$, $\psi^{-1}(1)=\{p\}$, and $\varphi(x)<\varphi(p)$ for $x\neq p$;
- **(W3)** outside an open neighborhood $U_0\ni p$ with $\overline{U_0}\subset\operatorname{int}\Delta^{m-1}$, the simplex is covered by (possibly overlapping) compact sets $G_i$, $i\in\mathbb Z/N\mathbb Z$, $N\ge m$;
- **(W4)** for cyclic intervals $I_1,\dots,I_m$ covering $\mathbb Z/N\mathbb Z$, the residence regions $R_j=\bigcup_{i\in I_j}G_i$ satisfy the convex-hull separation $\bigcap_{j=1}^m\operatorname{co}(R_j)=\varnothing$;
- **(W5)** every non-fixed interior orbit that eventually stays outside $U_0$ admits a lifted itinerary $r_n\in\mathbb Z$ with $K^n(x)\in G_{r_n \bmod N}$, $r_{n+1}-r_n\in\{0,1\}$ and $r_n\to+\infty$;
- **(W6)** every maximal lifted residence block of length $\ell$ through $I_j$ entered at time $b$ satisfies $\ell\ge A_j\log^+_{C_j}\big(B_j/\varphi(K^b(x))\big)$ for constants $A_j,B_j>0$, $C_j>1$.

**Theorem.** If $K$ is a weak admissible Stein–Ulam type map, then for every $x\in\operatorname{int}\Delta^{m-1}\setminus\{p\}$ and every $s\in\mathbb N$ the vector Cesàro averages

$$A_n(K^s)(x)=\frac1n\sum_{k=0}^{n-1}K^{sk}(x)$$

do not converge. Consequently:

1. $K$ (and every power $K^s$) has vector-valued historic behavior on a set of full relative $(m-1)$-dimensional Lebesgue measure;
2. the empirical measures $\mu_n^x=\frac1n\sum_{k<n}\delta_{K^k(x)}$ do not converge weak-* for any such $x$, so $K$ has no physical measure whose basin has positive Lebesgue measure;
3. for each $x$ and $s$, at least one coordinate average $\frac1n\sum_{k<n}(K^{sk}(x))_i$ diverges (the coordinate may depend on $x$).

## Expansion

By (W2), $\varphi(K^n(x))=\varphi(x)\prod_{k<n}\psi(K^kx)$ decreases to $0$ away from $p$, so interior orbits drift to the boundary and $\omega(x)\subset\partial\Delta^{m-1}$. By (W5) the orbit keeps cycling through all residence regions $R_1,\dots,R_m$, and by (W6) each visit lasts a time logarithmic in $1/\varphi$, which grows without bound as the orbit approaches the boundary. Each residence block is therefore long enough to drag the running average into a neighborhood of $\operatorname{co}(R_j)$ infinitely often for every $j$; if the averages converged to a point $a$, then $a$ would lie in every $\operatorname{co}(R_j)$, contradicting (W4). The same block structure survives sampling along $sk$ (and along multiplicatively thick subsequences). This is a discrete, simplex-valued analogue of the heteroclinic-cycle mechanism behind non-convergent time averages in May–Leonard and rock–paper–scissors Lotka–Volterra dynamics; the topological entropy of such maps is carried entirely by the boundary.

## Sources

- Farrukh Mukhamedov, "Full-measure historic behavior and emergence in simplex dynamics", arXiv:2609.18979 (2026), Definition 3.3 (weak admissible maps), Theorem 5.1, Corollaries 5.2–5.3, Theorem 6.2 and Corollary 6.3, <https://doi.org/10.48550/arXiv.2609.18979>.
