# Ancestral recombination trees and the explicit solution of discrete-time recombination

Let $(F_\tau)$ be the [segmentation process](segmentation-process-for-discrete-time-single-crossover-recombination.md) with crossover probabilities $\varrho_\alpha$, and for a contiguous set of links $\tilde L$ let $\mathcal L^{(\tilde L)}_G$ be the segments of $\tilde L \setminus G$. The probability that nothing happens in one step from state $G$ is

$$\lambda^{(\tilde L)}_G = \prod_{I \in \mathcal L^{(\tilde L)}_G} \Big( 1 - \sum_{\alpha\in I} \varrho_\alpha \Big), \qquad G \subseteq \tilde L,$$

and $\lambda_G = \lambda^{(L)}_G$. These numbers are the generalized eigenvalues of the linearized discrete-time recombination dynamics.

**Ancestral recombination trees.** Each path of the segmentation process that ends in $F_\tau = G$ is recorded by a full binary tree topology $T = (G, m)$ whose internal nodes are the links of $G$: the initial branching point $\gamma$ is the first link cut, and $m(\alpha)$ is the earlier cut that created the segment in which $\alpha$ was later cut. For $\alpha \in G$ let $I_\alpha$ be the segment containing $\alpha$ determined by its ancestors in $T$.

**Theorem (ART probabilities; Baake–von Wangenheim, Section 3.6).** The probability that the segmentation process has followed the tree topology $T = (G,m)$ by time $\tau$ is $\lambda_\varnothing^\tau$ if $G = \varnothing$, and otherwise

$$P_\tau(T) = \sum_{\gamma \in H \subseteq G} (-1)^{|H|-1} \Big[ \big(\lambda_{G_\gamma(H)}\big)^\tau - \big(\lambda_\varnothing\big)^\tau \Big] \prod_{\alpha\in G} \frac{\varrho_\alpha}{\lambda^{(I_\alpha)}_{G_\alpha(H)} - \lambda^{(I_\alpha)}_\varnothing},$$

where $G_\alpha(H)$ is the set of internal nodes of the subtree of $T$ rooted at $\alpha$ when $T$ is decomposed at the nodes of $H$. Consequently the discrete-time recombination equation has the explicit solution $p_t = \sum_{G} a_G(t) R_G(p_0)$ with $a_G(t) = \sum_m P_t((G,m))$, the sum running over all tree-consistent ancestor maps $m$.

**Example (four sites).** For $L = \{\tfrac12,\tfrac32,\tfrac52\}$, the two trees ending in $\{\tfrac12,\tfrac32\}$ (cut $\tfrac12$ first, or cut $\tfrac32$ first) give

$$P\big(F_\tau = \{\tfrac12,\tfrac32\}\big) = \varrho_{\frac12}\varrho_{\frac32} \sum_{k=0}^{\tau-2} \lambda_\varnothing^{k} \sum_{i=0}^{\tau-2-k} \lambda_{\{\frac12\}}^{i}\, \lambda_{\{\frac12,\frac32\}}^{\tau-2-k-i} + \varrho_{\frac12}\varrho_{\frac32}(1-\varrho_{\frac52}) \sum_{k=0}^{\tau-2} \lambda_\varnothing^{k} \sum_{i=0}^{\tau-2-k} \lambda_{\{\frac32\}}^{i}\, \lambda_{\{\frac12,\frac32\}}^{\tau-2-k-i},$$

where the factor $1 - \varrho_{\frac52}$ keeps the segment $\{\tfrac52\}$ uncut at the step when $\tfrac12$ is cut.

## Depends on

- [Segmentation process for discrete-time single-crossover recombination](segmentation-process-for-discrete-time-single-crossover-recombination.md)

## Expansion

A path to $G$ is a sequence of waiting periods separated by cutting events; while the state is $K$ the process stays put with probability $\lambda_K$ per step, and a cut at $\alpha$ inside a segment occurs with probability $\varrho_\alpha$ times the probability that the other segments stay uncut. Summing the resulting products of geometric weights over all times of the cuts gives nested geometric sums such as those in the example. The marginalization property of the segmentation process (its restriction to a contiguous block of links is again a segmentation process) lets the sum over times factor along subtrees, and partial fractions turn the nested sums into the signed combination of $\lambda^\tau$ terms; the denominators are nonzero because $\lambda_{G_\alpha(H)} > \lambda_\varnothing$ on the relevant segments.

## Sources

- E. Baake and U. von Wangenheim, *Single-crossover recombination and ancestral recombination trees*, *Journal of Mathematical Biology* 68 (2014), 1371–1402, <https://doi.org/10.1007/s00285-013-0662-x>; preprint arXiv:1206.0950, <https://doi.org/10.48550/arXiv.1206.0950>.
