# Eventual maximal multipoint Seshadri constants on surfaces

For every smooth integral projective complex surface $S$ and ample line bundle $L$ there exists $r_0>0$ such that for every integer $r\ge r_0$ one can remove countably many proper closed subsets of the ordered distinct complex $r$-point configuration space, with nonempty complement. For each configuration $p$ in that complement there is a blowup $\pi:B\to S$ of its point ideal with exceptional invertible ideals $\mathcal O_B(-E_i)$. Here $B$ is itself a smooth integral projective complex surface (with its closed embedding into complex projective space), and $\pi$ commutes with the two specified structure morphisms to $\operatorname{Spec}\mathbb C$. Moreover, $\pi^* L-\sqrt{L^2/r}\sum_i E_i$ has nonnegative degree on every integral curve of $B$. At the same $p$ the infimum of $\deg(L|_C)/\sum_i\operatorname{mult}_{p_i}(C)$ over integral curves $C$ with positive denominator equals $\sqrt{L^2/r}$. The threshold may depend on $(S,L)$.

Here the source computes $L^2=\chi(L^{\otimes2})-2\chi(L)+\chi(\mathcal O_S)$ and line-bundle degree on a curve by the difference of Euler characteristics. At a point of $C$, multiplicity is the least $n$ for which the stalk ideal of $C$ is not contained in the $(n+1)$-st power of the maximal ideal, and it is zero off $C$. The blowup represents morphisms making the point ideal invertible, with each exceptional ideal representing the pullback of the corresponding point ideal.

## Depends on

- Surface and curve cohomology, intersection and stalk multiplicity, configuration-space Zariski topology, and universal blowups with individual exceptional ideals.

## Proof depends on

- Very-general nefness of the explicit boundary class and the link between nefness, curve ratios, and the square-root upper bound.

## Expansion

Separate the projective blowup and degree comparisons from the eventual nefness argument. Then prove both the realization of the boundary class and the equality of the infimum on the same open-complement locus.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MaximalSeshadriConstants.lean#L408-L411) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MaximalSeshadriConstants.lean).
