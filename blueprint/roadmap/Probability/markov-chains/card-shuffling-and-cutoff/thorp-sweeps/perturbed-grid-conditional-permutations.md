# Conditional permutations on product grids

A grid has $b>0$ coordinates, coordinate $j$ of bit width $b_j\in\mathbb N$ and side length $m_j=2^{b_j}$. Its slots are tuples of $b_j$-bit words, with total size $s=\prod_j m_j$. An allowed grid at natural scale $r$ has $r\le b_j\le 2r$ for every $j$, so its side lengths are in $[2^r,2^{2r}]$. A line $L$ at stage $j$ fixes every coordinate other than $j$. Independently for every $(j,L)$, choose a permutation of that line with law $(1-z)U_j+zB_j$, where $U_j$ is uniform on its symmetric group and $B_j$ is the direct binary coordinate-sweep law on its bit positions. Stages act in order, with coordinate zero first. Let $w_z(\omega)$ be the product of the line-choice probabilities for the array $\omega$.

A trajectory system $H$ gives $h$ paths, with pairwise distinct slots at each of the $b+1$ stage boundaries and only coordinate $j$ allowed to change at stage $j$. An array is compatible if every partial sweep sends each initial marked slot to its prescribed slot at that boundary; feasibility means that at least one such array exists. Let $E_H$ be the compatible event and $p_z(H)=\sum_{\omega\in E_H}w_z(\omega)$. For a feasible system take a choice-selected compatible reference sweep $\pi_0$. The residual permutation for $\omega\in E_H$ is $\pi_0^{-1}\pi_\omega$, which fixes each marked initial slot. For a unitary irreducible representation $\rho$ of this stabilizer the conditional matrix is

$$
Q=p_z(H)^{-1}\sum_{\omega\in E_H}w_z(\omega)\rho(\pi_0^{-1}\pi_\omega).
$$

On the stated perturbation intervals the uniform component gives positive mass to every feasible event. The Schatten moment is $\operatorname{Re}\operatorname{tr}((Q^*Q)^q)$, **without division by the representation dimension**. The trace convention does not remove the event-probability denominator in $Q$. The extended log of a zero moment is $-\infty$. More generally the event distance on a nonempty finite choice set $E$ is the sum over $\omega\in E$ of the absolute difference of $w_z(\omega)/\sum_E w_z$ and $w_0(\omega)/\sum_E w_0$, without a factor of $1/2$.

If $h_{jL}$ counts the paths in line $L$ just before stage $j$, the visit cost is $C(H)=\sum_{j,L}\log(m_j^{h_{jL}}/(m_j)_{h_{jL}})$, with $(m)_k$ the falling factorial. Set $a=1/100$, $c_0=e_0=a/100$, $c(s)=c_0+1/\sqrt{\log s}$ and $e(s)=e_0-1/\sqrt{\log s}$, using the totalized real operations of the source.

## Depends on

- [Coordinate-fiber sweeps on the binary cube](binary-sweep-step-law.md)

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoordinateSweeps.lean#L19-L228)
