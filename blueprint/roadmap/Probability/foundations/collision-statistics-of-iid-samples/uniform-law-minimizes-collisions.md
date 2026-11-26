# The uniform law minimizes the probability of a repeat among i.i.d. samples

Let $\alpha$ be a finite set with $n$ elements and let $\mu$ be any probability distribution on $\alpha$. For $k$ i.i.d. samples $x_1, \dots, x_k$ from $\mu$,

$$
\Pr[x_1, \dots, x_k \text{ pairwise distinct}] \le \frac{n(n-1)\cdots(n-k+1)}{n^k},
$$

with equality when $\mu$ is uniform. Hence the probability of a collision ($x_i = x_j$ for some $i < j$) is minimized by the uniform law.

## Proof sketch

The probability of distinctness is the sum, over injective $k$-tuples, of products of point masses, a multilinear symmetric function of the weights. Adding the points of $\alpha$ one at a time, the tangent-line form of Bernoulli's inequality shows that the sum is largest for equal weights, a weak form of Maclaurin's inequality.

## Depends on

- [The exact collision probability](../../../ComputerScience/cryptography/hash-functions/birthday-bound/collision-prob-eq.md)
- [Uniform distribution on a finite type](../../distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Proof depends on

- [The exact collision probability](../../../ComputerScience/cryptography/hash-functions/birthday-bound/collision-prob-eq.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
