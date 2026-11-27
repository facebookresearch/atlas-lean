# Tracial group factors, ICC and property T

For a discrete countable group $G$, use its left regular representation on $\ell^2(G)$: $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$. The group von Neumann algebra $L(G)$ is the bicommutant of the regular unitaries, with trace $\tau_G(a)=\langle\delta_1,a\delta_1\rangle$. Tracial isomorphism is complex-linear unital $*$-algebra isomorphism preserving the trace and normal in both directions, expressed by preservation of suprema of families of projections (ordered by $pq=p$ for $p\le q$).

The ICC requirement here includes $G$ infinite and every nonidentity conjugacy class infinite. Kazhdan's property T means that any unitary representation on a complex Hilbert space with almost invariant unit vectors has a nonzero invariant vector: for every finite $K\subseteq G$ and $\varepsilon>0$ there is a unit vector $\xi$ with $\|\pi(g)\xi-\xi\|<\varepsilon$ for all $g\in K$. In the pinned statement the representation Hilbert space is in the universe of the group carrier.

## Expansion

Use the regular-representation and von Neumann algebra API, prove the trace and factor properties for ICC groups, and check the equivalence of projection-supremum normality with the intended notion. Audit the representation universe and preserve the divergence between abstract group and tracial factor isomorphisms.

## Sources

- [Pinned groups and property T](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/E_ConnesRigidity.lean#L7-L56)
- [Pinned group factors, trace and normal isomorphisms](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/E_ConnesRigidity.lean#L124-L189)
