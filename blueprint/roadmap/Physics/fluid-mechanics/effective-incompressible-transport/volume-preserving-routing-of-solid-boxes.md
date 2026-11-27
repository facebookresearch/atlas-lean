# Effective volume-preserving routing of solid boxes

Let $n\ge0$. For each $i<n$ in $\mathbb R^3$ take source and target closed boxes with rational centers $a_i,b_i$ and strictly positive rational half-widths $h_{ij},k_{ij}$ in each coordinate $j=0,1,2$. The source boxes are pairwise disjoint and the target boxes are pairwise disjoint; no condition forbids a source from intersecting a target. Require $\prod_j k_{ij}/h_{ij}=1$ for each $i$.

There exist a smooth, compactly supported spacetime field $U:\mathbb R\times\mathbb R^3\to\mathbb R^3$ and a global flow $\Phi$ such that $\operatorname{div}_x U=0$, $U(t,x)=0$ for $t\notin[1/4,3/4]$, $\Phi(0,x)=x$, and for every $x$ the curve $\Phi(t,x)$ is the unique all-real-time solution with derivative $U(t,\Phi(t,x))$. For each $i$ there is an open neighborhood of the **whole** source box on which the time-one map is exactly

$$ (\Phi(1,x))_j=b_{ij}+(k_{ij}/h_{ij})(x_j-a_{ij}). $$

Effectivity means there are computable evaluation, modulus and bound functions for all lists $\alpha$ of time and coordinate derivative directions: given $\alpha$, rational spacetime point $q$, precision $m\ge0$ and coordinate $j$, evaluation returns a rational $e$ with $|D^\alpha U_j(p)-e|\le 1/(m+1)$ at every real point $p$ satisfying $\|p-q\|\le 1/(1+M(\alpha,m))$. The norm here is the product norm on $\mathbb R\times(\mathrm{Fin}(3)\to\mathbb R)$, using the maximum coordinate norm on the finite product. The third function gives a global natural-number bound for $|D^\alpha U_j|$ at all spacetime points and coordinates. The empty list means $U$ itself.

## Expansion

Separate the volume-preserving diagonal deformation, parking translations, and routing stages. Prove that the local divergence-free generators extend with compact support and agree on neighborhoods, even when the source and target families overlap. Verify derivative bounds and computable moduli after gluing; flow uniqueness then yields the exact time-one map.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BalancedBoxRouting.lean#L15-L92) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/376.md).
- OpenAI, [Incompressible Box Transport and Finite Computation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Incompressible-Box-Transport-and-Finite-Computation-September-27-2026/manuscript.pdf) (September 27, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
