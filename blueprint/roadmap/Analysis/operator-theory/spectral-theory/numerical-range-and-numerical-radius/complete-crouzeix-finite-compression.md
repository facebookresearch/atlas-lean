# Finite compression of polynomial evaluation on a tensor vector

Let $H$ be a complex inner product space, not required complete, $A$ a bounded operator, $B_0,\ldots,B_d$ complex $m$-by-$m$ matrices and $\xi\in H\otimes\mathbb C^m$ an algebraic tensor. There is a finite-dimensional subspace $E\subset H$ and a vector $\eta$ in the completion of $E\otimes\mathbb C^m$ whose image under the completed tensor inclusion $J:E\widehat\otimes\mathbb C^m\to H\widehat\otimes\mathbb C^m$ equals the image of $\xi$ and such that

$$J\left(\sum_{k=0}^d ((P_EA)|_E)^k\otimes B_k\right)\eta=\left(\sum_{k=0}^d A^k\otimes B_k\right)\xi.$$

Here $P_E$ is orthogonal projection onto $E$; no positivity hypothesis on the natural number $m$ is imposed.

## Depends on

- The completed tensor inclusion of a finite-dimensional orthogonally projected subspace.

## Proof depends on

- Finite tensor support and containment of the resulting finite orbit segments under $A$ through degree $d$.

## Expansion

Establish the tensor embedding and compatibility with completion. Build $E$ from a finite pure-tensor presentation and the first $d$ iterates of its $H$ components, then verify the compressed powers on those components before summing.

## Sources

- OpenAI, [HilbertCrouzeix comparator, exists_finite_compression](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HilbertCrouzeix.lean#L121-L130).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/325.md).
