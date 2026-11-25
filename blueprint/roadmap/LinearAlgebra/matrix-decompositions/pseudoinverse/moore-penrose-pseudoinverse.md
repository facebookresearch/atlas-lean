# Pseudoinverse of a linear map

Let $V$ and $W$ be inner product spaces over $\mathbb F$, where $\mathbb F$ is $\mathbb R$ or $\mathbb C$, with $V$
finite-dimensional, and let $T \colon V \to W$ be a linear map. The range of $T$ is finite-dimensional, and the
restriction of $T$ to the orthogonal complement $(\operatorname{null} T)^\perp$ of the null space of $T$ is a linear
bijection from $(\operatorname{null} T)^\perp$ onto $\operatorname{range} T$. The pseudoinverse of $T$ is the linear map
$T^\dagger \colon W \to V$ given by

$$T^\dagger w = \big(T|_{(\operatorname{null} T)^\perp}\big)^{-1} \big(P_{\operatorname{range} T}\, w\big), \qquad w \in W,$$

where $P_{\operatorname{range} T}$ is the orthogonal projection of $W$ onto the finite-dimensional subspace
$\operatorname{range} T$: every $w \in W$ is $p + q$ for exactly one $p \in \operatorname{range} T$ and one
$q \in (\operatorname{range} T)^\perp$, and $P_{\operatorname{range} T}\, w = p$. Thus $T^\dagger w = 0$ when $w \in (\operatorname{range} T)^\perp$, and when
$w \in \operatorname{range} T$, $T^\dagger w$ is the unique vector of $(\operatorname{null} T)^\perp$ that $T$ maps
to $w$.

## Proof

The range of $T$ is finite-dimensional by the rank–nullity theorem, and $\operatorname{null} T$ is finite-dimensional as a
subspace of $V$. Finite-dimensional subspaces are complete, and complete subspaces have orthogonal projections: every
$v \in V$ is $a + u$ with $a \in \operatorname{null} T$ and $u \in (\operatorname{null} T)^\perp$, and every $w \in W$ is
$p + q$ with $p \in \operatorname{range} T$ and $q \in (\operatorname{range} T)^\perp$. Such a decomposition is unique,
because a vector lying in a subspace and in its orthogonal complement is orthogonal to itself, hence $0$. As $Tv = Tu$,
the restriction of $T$ to $(\operatorname{null} T)^\perp$ has the same range as $T$; it is injective, because a vector of
$(\operatorname{null} T)^\perp$ that $T$ maps to $0$ also lies in $\operatorname{null} T$. It is therefore a linear
bijection onto $\operatorname{range} T$, and its inverse is linear. Finally $P_{\operatorname{range} T}\, w = w$ when
$w \in \operatorname{range} T$, and $P_{\operatorname{range} T}\, w = 0$ when $w \in (\operatorname{range} T)^\perp$, which
gives the last two assertions.

## Depends on

- [Finite-dimensional vector space](../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Rank–nullity theorem](../../linear-maps-and-duality/rank-of-a-linear-map/rank-nullity-theorem/rank-nullity.md)
- [A complete subspace has an orthogonal projection](../../../Analysis/hilbert-spaces/of-complete-space.md)
- [Finite-dimensional subspaces are complete](../../../Topology/topological-modules/complete-of-finite-dimensional.md)

## Proof depends on

- [Every subspace of a finite-dimensional space is finite-dimensional](../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional-submodule.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 6.68, with 6.49, 6.55 and 6.67 (version read: the open-access PDF dated 4 November 2026).
