# Upstream resource concentration wins two-species stream competition

**Model.** Two species with densities $\mathbf u, \mathbf v$ share a homogeneous flow stream network $(G, f, L)$, $L = dD + qQ$, with a common carrying capacity $k > 0$:

$$\frac{du_i}{dt} = \sum_{j} (dD_{ij} + qQ_{ij})\,u_j + r_i u_i\Big(1 - \frac{u_i + v_i}{k}\Big), \qquad \frac{dv_i}{dt} = \sum_{j} (dD_{ij} + qQ_{ij})\,v_j + s_i v_i\Big(1 - \frac{u_i + v_i}{k}\Big),$$

with nonnegative, nonzero initial data. The two species move identically and differ only in their resource (growth-rate) distributions $\mathbf r, \mathbf s > \mathbf 0$. The model has semitrivial equilibria $E_1 = (\mathbf u^*, \mathbf 0)$ and $E_2 = (\mathbf 0, \mathbf v^*)$.

**Theorem.** Let $\sum_i r_i = \sum_i s_i = r > 0$ (equal total resources). Suppose $r_i = 0$ at every node with $f(i) > 0$ (species $\mathbf u$ puts all its resources at the upstream ends), and $s_{i_0} > 0$ at some node with $f(i_0) > 0$. Then $E_1 = (\mathbf u^*, \mathbf 0)$ is globally asymptotically stable: species $\mathbf u$ excludes species $\mathbf v$.

So the allocation that maximizes total single-species biomass is also the competitively dominant one. In the three-node configurations with one upstream node feeding two downstream nodes, the same holds for $\mathbf r = (r, 0, 0)$ against any $\mathbf s \ne \mathbf r$ with the same total.

## Depends on

- [Total biomass bound in homogeneous flow stream networks](total-biomass-bound-in-homogeneous-flow-stream-networks.md)

## Expansion

The system is competitive, hence monotone for the order induced by the cone $\mathbb R^n_+ \times (-\mathbb R^n_+)$. By the standard trichotomy for such systems, if $E_2$ is linearly unstable and there is no positive equilibrium, then $E_1$ attracts every solution with $\mathbf u_0 > \mathbf 0$. Instability of $E_2$ reduces to the sign of the principal eigenvalue of $dD + qQ + \operatorname{diag}(r_i(1 - v^*_i/k))$. A positive equilibrium is ruled out by a sign-pattern graph: each node is labeled by whether the total density $w_i = u_i + v_i$ is below, above or at $k$, and each edge by the direction of the net flow $(d+q)w_i$ versus $d\,w_j$. Flow-balance constraints at each node then leave no admissible sign pattern.

## Sources

- Tung D. Nguyen, Yixiang Wu, Tingting Tang, Amy Veprauskas, Ying Zhou, Behzad Djafari Rouhani and Zhisheng Shuai, "Impact of resource distributions on the competition of species in stream environment", Journal of Mathematical Biology 87 (2023), 62, <https://doi.org/10.1007/s00285-023-01978-6>; numbering as in arXiv:2306.05555: Lemma 2.2, Theorem 3.6, Theorem 4.5 and its proof (Lemmas 4.6 to 4.14).
