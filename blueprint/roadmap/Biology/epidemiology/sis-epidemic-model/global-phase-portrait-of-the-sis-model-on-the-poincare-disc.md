# Global phase portrait of the SIS model on the Poincaré disc

**Setting.** For a population of constant size $k>0$ with births $mk$, per-capita death rate $m$, infectivity $b$ and recovery rate $c$, the susceptible–infected–susceptible (SIS) model is the quadratic planar system

$$\dot x=-bxy-mx+cy+mk,\qquad \dot y=bxy-(m+c)y,$$

with $x$ the susceptible and $y$ the infected part of the population. It is studied on the whole plane, compactified to the Poincaré disc, for $bm\neq0$. Its finite equilibria are the disease-free state $q=(k,0)$ and the state $p=\big(\tfrac{m+c}{b},\,k-\tfrac{m+c}{b}\big)$, which is endemic (positive $y$) exactly when $bk>m+c$.

**Theorem.**
1. (Invariant lines) The lines $y=0$ and $x+y=k$ are invariant, and so is $x=k$ when $c=bk$.
2. (Finite equilibria) If $m>0$ and $m>bk-c$, or $m<0$ and $m<bk-c$, then $p$ is a saddle and $q$ a node. If $m>0$ and $m<bk-c$, or $m<0$ and $m>bk-c$, then $p$ is a node and $q$ a saddle. If $m=bk-c$, then $p=q$ is a semi-hyperbolic saddle-node.
3. (Infinity) The infinite singular points are the origins of the four standard charts, all saddle-nodes, together with one node at infinity.
4. (Global classification) Up to topological equivalence and reversal of time, the phase portrait on the Poincaré disc is one of exactly two: the generic portrait with one saddle and one node among $p,q$ (case 2, first two alternatives), and the degenerate portrait with a single saddle-node (case $m=bk-c$).

For the biologically relevant case $m>0$, the condition $bk>m+c$, i.e. $\mathcal R_0=bk/(m+c)>1$, is exactly the condition under which the endemic state $p$ is the node and the disease-free state $q$ is a saddle; at $\mathcal R_0=1$ the two equilibria merge into a saddle-node (a transcritical exchange of stability).

## Expansion

At $q$, translated to the origin, the Jacobian has determinant $\delta=-(bk-c-m)m$ and trace $\tau=bk-c-2m$, and $\tau^2-4\delta=(c-bk)^2\ge0$, so $q$ is a saddle when $\delta<0$ and a node when $\delta>0$; the same computation at $p$ gives the opposite sign of $\delta$. When $\delta=0$ but $\tau\ne0$, the center-manifold reduction (the classical theorem on semi-hyperbolic points) shows a saddle-node. Infinite singular points are found in the charts $U_i,V_i$ of the Poincaré compactification and analyzed the same way. With the invariant lines separating the disc and the local pictures fixed, the Poincaré–Bendixson theory (no periodic orbits can cross the invariant lines) leaves only the two global configurations.

## Sources

- Regilene D. S. Oliveira, Alex C. Rezende, "Global phase portraits of a SIS model", arXiv:1205.6015 (2012), system (1), system (1), Theorem 1.1, Propositions 3.1–3.3 and Section 4, <https://doi.org/10.48550/arXiv.1205.6015>.
