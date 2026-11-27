# Path-space large deviations for daily growth–mutation–selection chains

**Model.** A bacterial population of fixed size $N$ carries $g$ genotypes, with histogram $H_t \in \mathcal H = \{H \in [0,1]^g : \sum_j H(j) = 1\}$ at the start of day $t$. Each day:

1. **growth:** genotype $j$ multiplies by a fixed factor $F_j > 1$ ($F_1 < \dots < F_g$), so the histogram becomes $\Phi(H)$, $\Phi_j(H) = F_jH(j)/\langle F, H\rangle$;
2. **mutation:** the number of $j$-cells mutating is Poisson with mean $mNF_jH(j)$ (mutation rate $m \ll 1$), and a mutating $j$-cell becomes a $k$-cell with probability $q_{jk}$ ($q_{jj} = 0$);
3. **selection:** $N$ cells are sampled to form the next day's population.

This defines a Markov chain on $N$-rational histograms with one-step conditional mean $f(H) = \mathbb E[H_{t+1} \mid H_t = H]$; the **mean trajectory** is $\bar H_{t+1} = f(\bar H_t)$.

**One-step cost.** For interior histograms $H, G$ there is a smooth one-step cost $C(H,G) \ge 0$ with $\Pr(H_{t+1} \approx G \mid H_t = H) \approx e^{-NC(H,G)}$, vanishing only at $G = f(H)$, and for small $m$

$$C(H,G) = \mathrm{KL}\big(G \,\|\, \Phi(H)\big) + m\sum_{j,k}F_jH(j)q_{jk}\Big[1 - \frac{U_k}{U_j}\Big] + O(m^2), \qquad U_j = \exp\Big(\frac{G_j}{F_jH(j)}\Big).$$

**Theorem (large deviations on tubes of paths).** For paths $\mathbf h = (H_1,\dots,H_T)$ set $\lambda(\mathbf h) = \sum_{t=1}^{T-1}C(H_t, H_{t+1})$ and $\Lambda(A) = \inf_{\mathbf h \in A}\lambda(\mathbf h)$. For every interior path $\mathbf h$ and interior tube $\mathcal T(\mathbf h,\epsilon)$ of paths within sup-distance $\epsilon$, the random histogram path started at $H_1$ satisfies

$$\frac1N\log P_N(\hat{\mathbf h} \in \mathcal T) \to -\Lambda(\mathcal T) \quad (N \to \infty),$$

and thin tubes $\mathcal T(\mathbf h, 1/N)$ have probability log-equivalent to $e^{-N\lambda(\mathbf h)}$. Consequently the mean trajectory is the unique zero-cost path, and the **most likely path** from $H$ to a rare target $G$ (e.g. emergence of a non-dominant genotype) in $T$ days minimizes $\lambda$ over paths with these endpoints.

## Expansion

Without mutation, one day is multinomial sampling from $\Phi(H)$, whose Cramér rate is exactly the relative entropy $\mathrm{KL}(G\|\Phi(H))$ (Sanov's theorem); rare Poisson mutations add the $O(m)$ correction. Markov additivity turns one-step costs into the path functional $\lambda$. The minimization over paths is a discrete optimal-control problem; it can be solved by reverse-time geodesic shooting with gradients of $C$, which scales to many genotypes.

## Sources

- Yingxue Su, Brett Geiger, Ilya Timofeyev, Andreas Mang and Robert Azencott, "Rare events analysis and computation for stochastic evolution of bacterial populations", *Stochastic Analysis and Applications* 43 (2025), 1–29, <https://doi.org/10.1080/07362994.2024.2422913>. Numbering as in the preprint arXiv:2308.14135v1, <https://arxiv.org/abs/2308.14135v1>: Section 2 (model), Section 3 (cost expansion and Theorem 3.1), Sections 4–5 (geodesic shooting).
