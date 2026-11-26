# A noninvertible C¹ map with zero entropy and homological growth

There exist an integer $q>0$ and a nonbijective continuous self-map $f$ of $X_q=S^1\times(S^2)^{q+1}$, with $5\le 2q+3$. Use the standard embeddings as unit spheres in $\mathbb R^2$ and $\mathbb R^3$. At each embedded point $x$, the map agrees on an open ambient neighborhood of $x$ intersected with $X_q$ with a $C^1$ map into the ambient product space. Its uniform dynamical-cover entropy (`coverEntropy`) on all of $X_q$ equals zero; on this compact space it agrees with open-cover entropy.

Writing $f_{*,n}$ for the induced map on real singular homology, there is a nonzero $v\in H_2(X_q;\mathbb R)$ with $f_{*,2} v=2v$. For the spectral expression, take the supremum $\rho$ of $\sqrt{a^2+b^2}$ over all $n\ge0$ and all real $a,b$ for which there are $u,v\in H_n(X_q;\mathbb R)$, not both zero, with

$$ f_{*,n}u=au-bv,\qquad f_{*,n}v=bu+av. $$

The source requires $0<\log 2\le\log\rho$. Thus the proposed example concerns the entropy lower bound for general noninvertible $C^1$ self-maps; it makes no assertion about smooth diffeomorphisms or maps on all manifolds.

## Depends on

- [Topological entropy](topological-entropy.md)
- [Cover entropy comparison](cover-entropy-eq-topological-entropy.md)

## Expansion

Construct the clock/sphere map with the stated ambient differentiability. Compute its action on real singular $H_2$ and show the set defining $\rho$ is nonempty and bounded by using finite-dimensionality and the finite range of nonzero homology degrees. Separately bound its orbit-cover growth and verify nonbijectivity.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/C1EntropyCounterexample.lean#L11-L67) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/151.md).
- OpenAI, [A $C^1$ Counterexample to the Entropy Conjecture](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-C1-Counterexample-to-the-Entropy-Conjecture-September-25-2026/article.pdf) (September 25, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
