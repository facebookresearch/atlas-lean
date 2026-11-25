# Lieb's concavity theorem, case `q = 0`

For a complex $m \times n$ matrix $K$ and $0 \le r \le 1$, the map $(A, B) \mapsto \operatorname{Re} \operatorname{tr}(K^* A^0 K B^r)$ is jointly concave on pairs of positive definite matrices, $A$ of size $m$ and $B$ of size $n$. This is the instance $q = 0$ of Lieb's concavity theorem (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 6.1), in the form of the [joint statement](lieb-concavity-trace-rpow.md); since $A^0 = 1$ and $\operatorname{tr}(K^* K B^r) = \operatorname{tr}(K B^r K^*)$, it reduces to the concavity of $B \mapsto \operatorname{Re} \operatorname{tr}(K B^r K^*)$.

This is a restricted case: with $q = 0$ the map depends on one matrix only, so its joint concavity is one-variable concavity. The joint concavity for $q, r > 0$ is the substance of Lieb's theorem; this case is its boundary $q = 0$.

## Informally uses

- [Concavity of `A ↦ tr (K* A^q K)`](concave-on-re-trace-conj-rpow.md): the one-variable concavity applied to $K^*$ after the cyclic rewriting.

## Background

- [Lieb's concavity theorem, joint form](lieb-concavity-trace-rpow.md): the joint statement, whose boundary instance $q = 0$ this is.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009, Theorem 6.1. Theorem numbers refer to that draft.
