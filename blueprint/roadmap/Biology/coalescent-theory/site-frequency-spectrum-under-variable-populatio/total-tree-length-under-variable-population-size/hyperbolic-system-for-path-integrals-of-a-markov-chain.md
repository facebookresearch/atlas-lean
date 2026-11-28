# Hyperbolic system for path integrals of a Markov chain

**Setting.** Let $X(t)$ be a regular right-continuous jump Markov process on $\{1,\dots,n\}$ with time-dependent conservative generator $Q(t)=(q_{ij}(t))$, $Q\in C(\mathbb{R}_+)\cap L^\infty(\mathbb{R}_+)$, such that for each state $i$ either $q_i(t)=-q_{ii}(t)=0$ for all $t$ or $q_i(t)>0$ for all $t$ with $\int_0^\infty q_i(s)\,ds=\infty$. For a function $\mathbf v=(v_1,\dots,v_d):\{1,\dots,n\}\to\mathbb{R}^d$ define the path integral and the distribution vector

$$
\mathbf L^{\mathbf v}(t)=\int_0^t\mathbf v(X(s))\,ds,\qquad F_k^{\mathbf v}(t,\mathbf x)=\mathbb{P}\bigl\{X(t)=k,\ \mathbf L^{\mathbf v}(t)\le\mathbf x\bigr\},
$$

with componentwise comparison, and $\mathbf F^{\mathbf v}=(F_1^{\mathbf v},\dots,F_n^{\mathbf v})$ as a row vector.

**Proposition.** If $\mathbf F^{\mathbf v}$ is Lipschitz continuous on an open set $\mathcal U\subset\mathbb{R}_+\times\mathbb{R}^d$, then

$$
\partial_t\mathbf F^{\mathbf v}(t,\mathbf x)+\sum_{j=1}^d\partial_{x_j}\mathbf F^{\mathbf v}(t,\mathbf x)\,V_j=\mathbf F^{\mathbf v}(t,\mathbf x)\,Q(t)\qquad\text{a.e. in }\mathcal U,
$$

where $V_j=\mathrm{diag}(v_j(1),\dots,v_j(n))$. Moreover $F_k^{\mathbf v}(t,\mathbf x)\to\mathbf 1_{\mathbb{R}_+^d}(\mathbf x)\,\mathbb{P}\{X(0)=k\}$ as $t\to0^+$ for $\mathbf x\notin\partial\mathbb{R}_+^d$.

## Expansion

Over a short interval $[t,t+\varepsilon]$ the chain either stays in state $k$, in which case the path integral moves deterministically by $\varepsilon\,\mathbf v(k)$, or jumps with probability $q_{ik}(t)\varepsilon+o(\varepsilon)$. Bounding $\mathbf L^{\mathbf v}(t+\varepsilon)$ between $\mathbf L^{\mathbf v}(t)+\varepsilon\mathbf m^{\mathbf v}$ and $\mathbf L^{\mathbf v}(t)+\varepsilon\mathbf M^{\mathbf v}$ (componentwise minima and maxima of $\mathbf v$) and letting $\varepsilon\to0$ gives the forward equation in which transport at speed $v_j(k)$ in direction $x_j$ is added to the Kolmogorov forward equation $\partial_t\mathbf p=\mathbf pQ(t)$. Each component is transported along its own characteristic, which makes the system linear hyperbolic and suited to the method of characteristics; when $\mathbf v$ is monotone along the paths and $Q$ is lower triangular, the solution is a strong solution in the region $\mathbf x<\mathbf M^{\mathbf v}t$ with explicit boundary values.

## Sources

- Alexey Miroshnikov and Matthias Steinrücken, "Computing the joint distribution of the total tree length across loci in populations with variable size", *Theor. Popul. Biol.* 118 (2017), 1-19. <https://doi.org/10.1016/j.tpb.2017.09.002>
- Preprint version (the locators in this item follow its numbering): Alexey Miroshnikov, Matthias Steinrücken, *Computing the joint distribution of the total tree length across loci in populations with variable size*, arXiv (2016). Appendix A: Definitions A.1–A.3, Proposition A.5, Proposition A.8, Proposition A.14. <https://doi.org/10.48550/arXiv.1609.08880>
