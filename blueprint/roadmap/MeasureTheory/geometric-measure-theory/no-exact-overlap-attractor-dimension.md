# Dimension of self-similar attractors without exact overlaps

Let $f_i(x)=r_ix+t_i$ for a nonempty finite family with $0<|r_i|<1$ and no two distinct nonempty finite words inducing the same affine map. For each infinite sequence $\omega$ of indices define $x(\omega)=\sum_{n\geq0}(\prod_{j<n}r_{\omega_j})t_{\omega_n}$. Its range $K$ is compact and nonempty. There is a unique real $s\geq0$ with $\sum_i |r_i|^s=1$, and $\dim_{\rm H}K=\min(1,s)$. The condition is on composition maps, not separation of the images $f_i(K)$; for one map the root is $s=0$.

## Depends on
- [Attractor convention](hausdorff-dimension-of-self-similar-sets/is-attractor.md), with a bridge from the signed coding-series range to the invariant compact set.

## Proof depends on

- [Entropy-rate formula](entropy-rate-dimension-self-similar-measures.md), for the lower bound at the weights $|r_i|^s$.

## Proof outline

Use uniform geometric-series convergence to obtain a continuous coding map from the compact nonempty product of the finite index set and identify its range. Bound cylinder diameters by products of the absolute ratios to obtain the upper bound, also bounded by 1 in the ambient line. Prove existence and uniqueness of the exponent, including the singleton case, and check the self-similar probability at those weights is carried by the range for the entropy lower bound. Do not assume the open set condition.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SelfSimilarCorollaries.lean#L78-L87) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/148.md).
