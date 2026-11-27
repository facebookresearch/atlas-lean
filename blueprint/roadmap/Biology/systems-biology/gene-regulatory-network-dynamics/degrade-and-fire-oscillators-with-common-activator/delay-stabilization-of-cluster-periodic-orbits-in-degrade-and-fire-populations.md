# Delay stabilization of cluster periodic orbits in degrade-and-fire populations

**Model.** $N$ degrade-and-fire (DF) oscillators with repressor concentrations $x_1,\dots,x_N\ge 0$ share an activator $A\ge 0$:

$$
\dot x_i(t)=-1\ \text{ if } x_i(t)>0,\qquad x_i(t^+)=R+\nu A(t-\tau)\ \text{ if } x_i(t)=0,\qquad
\dot A(t)=m(t)-\beta A(t),\quad m(t)=\frac1N\sum_{i=1}^N x_i(t),
$$

with parameters $R,\beta,\nu>0$, feedback delay $\tau\ge 0$, $\nu<\beta$ and $\tau<R$. Each repressor degrades linearly and is reset by a burst of synthesis ("firing") whose size grows with the delayed activator level; the activator integrates the mean repressor (quorum sensing). The firing order is preserved forever under

$$
\nu<\frac{\beta}{1+\beta R}. \tag{O}
$$

A trajectory is **partially synchronized** with cluster distribution $\{n_k\}_{k=1}^K$ ($\sum_k n_k=N$, $K<N$) if the oscillators form $K$ groups of equal concentration $y_k$; the distribution is invariant, and scaling all cluster sizes by $q\in\mathbb{N}$ maps partially synchronized trajectories to partially synchronized trajectories with the same $(y_k)$ and $A$. Consider fixed points of the return map to the section $y_K=0$.

**Stability criterion (Lemma 4.2).** Assume (O) and $\tau>0$. If a cluster fixed point is asymptotically stable inside its own partially synchronized subspace, its periodic orbit has no firing in any window $[-\tau,0]$ modulo the period, and $\dot A(-\tau)=m(-\tau)-\beta A(-\tau)<0$, then it is exponentially stable with respect to small perturbations that smear cluster $K$ into several nearby sub-clusters.

**Theorem (Fernandez–Tanzi, Theorem 4.4).** Assume (O). Let $\{n_k\}_{k=1}^K$ be given and suppose that, for $\tau=0$, the return map in the corresponding partially synchronized subspace has an exponentially stable fixed point $(\{n_k,y_k^{\mathrm{FP}}\},A^{\mathrm{FP}})$. Then:

1. there is $q_0\in\mathbb{N}$ such that, for $\tau=0$ and every $q>q_0$, the scaled fixed point $(\{qn_k,y_k^{\mathrm{FP}}\},A^{\mathrm{FP}})$ is unstable with respect to arbitrarily small perturbations of any of its clusters;
2. there is $\tau_0>0$ such that for every $\tau\in(0,\tau_0)$ and every $q\in\mathbb{N}$ the fixed point continues to delay $\tau$, and the continued fixed point is exponentially stable with respect to small perturbations that smear any of its clusters.

**Equi-distributed clusters (Lemma 4.5, Corollary 4.6).** For $\tau=0$ and every $N>1$ there is a unique fixed point with $N$ equally spaced clusters, $x_i-x_{i+1}=(R+\nu A^{\mathrm{FP}})/N$; for $N\in\{2,\dots,5\}$ it is exponentially stable in its own subspace once $\beta>\beta_N$. Hence, for such $N$ and $\beta$, these multi-cluster orbits are unstable to cluster smearing at $\tau=0$ for large populations but stable for all small $\tau>0$; several distinct stable (partially) synchronized oscillations can coexist.

## Depends on

- [Delay-dependent stability of synchrony in degrade-and-fire oscillators](delay-dependent-stability-of-synchrony-in-degrade-and-fire-oscillators.md)

## Proof sketch

At $\tau=0$ the activator value must be the same at each cluster firing, so $\dot A$ vanishes once between consecutive firings, being negative just before and positive just after each firing. By continuity these signs persist for small $\tau>0$. The negative sign before firing is exactly the hypothesis of the stability criterion (delayed sampling of a decreasing activator makes laggards receive smaller resets), while for $\tau=0$ the positive sign after firing exceeds the jump contributed by a single oscillator, of order $(R+\nu A^{\mathrm{FP}})/(qN)$, once $q$ is large, which triggers the instability criterion. Existence of the continued fixed point follows from the implicit function theorem applied to the composition of smooth firing maps.

## Sources

- Bastien Fernandez and Matteo Tanzi, "Feedback-delay dependence of the stability of cluster periodic orbits in populations of degrade-and-fire oscillators with common activator", *Journal of Mathematical Biology* 90 (2025), 27, <https://doi.org/10.1007/s00285-024-02169-7>. Preprint version: arXiv:2405.07752 (2024), <https://doi.org/10.48550/arXiv.2405.07752>.
