# Rank–nullity theorem

Let $V$ and $W$ be vector spaces over $\mathbb F$, where $\mathbb F$ is $\mathbb R$ or $\mathbb C$, with $V$
finite-dimensional, and let $T \colon V \to W$ be a linear map. Then the range
$\operatorname{range} T = \{Tv : v \in V\}$ is finite-dimensional, and

$$\dim V = \dim \operatorname{null} T + \dim \operatorname{range} T,$$

where $\operatorname{null} T = \{v \in V : Tv = 0\}$ is the null space of $T$, a subspace of $V$ and therefore
finite-dimensional.

## Proof

Let $u_1, \dots, u_m$ be a basis of $\operatorname{null} T$, which is finite-dimensional as a subspace of $V$. Extend it
to a linearly independent set of vectors of $V$ that spans $V$. This set is finite, since in a space spanned by finitely
many vectors a linearly independent family has at most as many members as the spanning set, the field $\mathbb F$ having
the strong rank condition; so it is a basis $u_1, \dots, u_m, v_1, \dots, v_n$ of $V$, and $\dim V = m + n$. Every
$Tu_k$ is $0$, so the vectors $Tv_1, \dots, Tv_n$ span $\operatorname{range} T$, which is therefore finite-dimensional.
They are linearly independent: if $c_1 Tv_1 + \dots + c_n Tv_n = 0$, then $c_1 v_1 + \dots + c_n v_n$ lies in
$\operatorname{null} T$, so it is a linear combination of $u_1, \dots, u_m$, and the linear independence of the basis of
$V$ forces every $c_j$ to be $0$. Hence $Tv_1, \dots, Tv_n$ is a basis of $\operatorname{range} T$, and
$\dim \operatorname{range} T = n = \dim V - m$.

## Depends on

- [Dimension of a finite-dimensional vector space](../../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimension.md)
- [Finite-dimensional vector space](../../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Every subspace of a finite-dimensional space is finite-dimensional](../../../bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional-submodule.md)

## Proof depends on

- [Every vector space has a basis](../../../bases-and-dimension/bases-and-coordinates/existence-of-bases/exists-basis.md)
- [Extending a linearly independent set within a larger set](../../../bases-and-dimension/bases-and-coordinates/existence-of-bases/exists-linear-indep-on-extension.md)
- [A linearly independent family is no larger than a finite spanning set](../../../bases-and-dimension/bases-and-coordinates/dimension/linear-independent-le-span.md)
- [Nonzero commutative rings have the strong rank condition](../../../bases-and-dimension/bases-and-coordinates/dimension/comm-ring-strong-rank-condition.md)
- [Basis of a vector space](../../../bases-and-dimension/bases-and-coordinates/bases/vector-space-basis.md)
- [Linearly independent family](../../../bases-and-dimension/bases-and-coordinates/bases/linear-independent.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 3.21 (version read: the open-access PDF dated 4 November 2026).
