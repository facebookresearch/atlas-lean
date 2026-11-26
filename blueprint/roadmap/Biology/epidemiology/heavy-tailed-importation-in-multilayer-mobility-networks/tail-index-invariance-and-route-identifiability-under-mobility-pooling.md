# Tail-index invariance and route identifiability under mobility pooling

**Setting.** Imported infections reach a region through routes $e \in \mathcal{R}$, each a (source, destination, layer) triple, where layers $\ell \in \mathcal{L}$ are transport modes (air, commuting, ...). A random vector $\mathbf{B}$ on $\mathbb{E} = [0,\infty)^d \setminus \{\mathbf{0}\}$ is *multivariate regularly varying* (MRV) with index $\tau > 0$, scaling $b(t)$ and nonzero Radon limit measure $\nu$ if $t\,\mathbb{P}(\mathbf{B}/b(t) \in \cdot) \to \nu$ vaguely; under the $\ell_1$ norm the angular part of $\nu$ is the probability spectral measure $H$ on the simplex $\mathbb{S}_+$.

**Results.**
1. *(Poisson sampling preserves magnitude.)* If $\mathbf{B}_i = (B_{i\ell})_\ell$ is MRV with index $\tau$ and limit $\nu$, $Q_i$ is an independent random positive diagonal matrix with $\mathbb{E}\|Q_i\|^{\tau + \epsilon} < \infty$, and the counts $\mathbf{Z}_i$ are conditionally Poisson with mean $Q_i \mathbf{B}_i$, then $\mathbf{Z}_i$ is MRV with the same index $\tau$ and limit measure $\mu_Z(A) = \mathbb{E}\,\nu\{\mathbf{b} : Q_i\mathbf{b} \in A\}$. Layer-specific reporting $Q_i$ leaves the tail index unchanged but reweights the angular (composition) part.
2. *(Aggregation.)* For a nonnegative $m \times |\mathcal{R}|$ matrix $S$ with no zero column, $S\mathbf{Z}$ is MRV with index $\tau$ and spectral measure

$$
H_S(A) = \frac{\int_{\mathbb{S}_+} \|Sw\|_1^{\tau}\, \mathbf{1}\{Sw/\|Sw\|_1 \in A\}\, H_R(dw)}{\int_{\mathbb{S}_+} \|Sw\|_1^{\tau}\, H_R(dw)} .
$$

3. *(Identifiability.)* Let $\hat s_e = s_e / \|s_e\|_1$ be the normalized columns of $S$. The map $T_S(w) = Sw/\|Sw\|_1$ is injective on $\mathbb{S}_+$ iff the signatures $\{\hat s_e\}$ are affinely independent; this needs $|\mathcal{R}| \le m$, so pooling to one aggregate ($m = 1$) is injective only for a single route. When injective, $H_R$ is recovered from $H_S$ by reweighting with $\|S\psi(v)\|_1^{-\tau}$, $\psi = T_S^{-1}$. Pooling layers within each source–destination pair identifies the source–destination spectral measure exactly, $H_{\mathrm{OD}} = H_R \circ S^{-1}$, but never the layer composition within a pair, since routes differing only in $\ell$ share a signature.

## Expansion

Regular variation is closed under independent multiplicative perturbations with lighter tails (Breiman's lemma), and Poisson noise around a heavy-tailed mean is asymptotically negligible, so the radial index survives sampling and any nonnegative linear aggregation. The angle is different: a linear map sends the simplex to the simplex only after renormalization, and the factor $\|Sw\|_1^{\tau}$ tilts the spectral measure toward directions that the aggregation amplifies. Recovering the route-level picture is then a question of whether $T_S$ can be inverted, which is affine independence of the route signatures. For mode-specific interventions this means that a pooled network can say how extreme the next importation will be, but not by which mode it will arrive.

## Sources

- T. Wang, W. Yang, "Pooling Mobility Obscures Epidemic Invasion Routes", arXiv:2608.25766 (2026), Theorem 2, Proposition 1, Corollary 1, Proposition 2, Lemmas 1–2, <https://doi.org/10.48550/arXiv.2608.25766>.
