# Consistency of the ML supertree under the exponential model of gene-tree error

In the **exponential model** of gene-tree estimation error, a gene tree $T'$ on leaf set $\mathcal{L} \subset \mathcal{L}^*$ is observed with density

$$
\mathcal{P}^{\mathcal{L}}_{T^*}(T') = \alpha_{T^*, \mathcal{L}} \exp\!\big(-\beta_{\mathcal{L}}\, d(T', T^*|_{\mathcal{L}})\big),
$$

where $T^*$ is the true species tree, $\beta_{\mathcal{L}} > 0$ depends only on $\mathcal{L}$, $\alpha_{T^*,\mathcal{L}}$ is the normalizing constant, and $d$ is a continuous tree distance on the space of metric trees that coincides with the Euclidean distance between branch-length vectors of trees sharing a topology (for example the BHV distance).

**Theorem.** Suppose the leaf sets $\mathcal{L}_1, \mathcal{L}_2, \dots$ of independently observed gene trees satisfy the weak covering property with exponent $\gamma > 1/2$ (every quartet of species is contained in at least $c_1 k^\gamma$ of the first $k$ leaf sets for large $k$). Then the exponential model is identifiable and regular, and for every $\delta > 0$ there are $C_\delta, K_\delta > 0$ such that for all $k \ge K_\delta$ the maximum likelihood supertree $\hat T_k$ satisfies

$$
d(\hat T_k, T^*) \le C_\delta \left( \frac{\log k}{k^{\gamma - 1/2}} \right)^{1/m}, \qquad m = 4 \sup_i |\mathcal{L}_i| - 4,
$$

with probability at least $1 - \delta$.

## Expansion

The result is the general convergence theorem applied after verifying its hypotheses for this model. Positivity and local Lipschitz continuity of $T \mapsto \mathcal{P}^{\mathcal{L}}_T(T')$ are immediate. For identifiability and the KL lower bound one uses Pinsker's inequality, $\mathrm{KL} \ge 2\, d_{TV}^2$, and bounds the total variation from below on the set $A$ of trees within distance $d(T|_{\mathcal{L}}, T^*|_{\mathcal{L}})/(3\beta_{\mathcal{L}})$ of $T^*|_{\mathcal{L}}$, where the two densities differ by a definite factor. Since $d$ is Euclidean inside an orthant of dimension $2|\mathcal{L}| - 3$, the Lebesgue measure of $A$ scales like $d^{\,2|\mathcal{L}|-3}$, and together with $e^{-x} - e^{-2x} \ge x/2$ for small $x$ this gives $d_{TV} \gtrsim d^{\,2|\mathcal{L}|-2}$, hence $\mathrm{KL} \ge C\, d^{\,4|\mathcal{L}|-4}$. Applying this only to observed leaf sets gives $m = 4\sup_i |\mathcal{L}_i| - 4$; the exponent is not claimed to be sharp.

## Depends on

- [Convergence rate of the maximum likelihood supertree](convergence-rate-of-the-maximum-likelihood-supertree.md)

## Proof depends on

- [Pinsker's inequality for probability measures](../../../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/of-real-two-mul-total-variation-dist-sq.md)

## Sources

- L. S. T. Ho and V. Dinh, *Convergence of maximum likelihood supertree reconstruction*, arXiv:2105.01723 (2021), Section 4, Theorem 2. <https://doi.org/10.48550/arXiv.2105.01723>
- M. Steel and A. Rodrigo, *Maximum likelihood supertrees*, Systematic Biology 57 (2008), origin of the exponential model and the covering property.
