# Search-to-decision reduction for LWE with prime modulus

Let $q$ be prime and polynomially bounded in $n$, and let $\chi$ be an error distribution on $\mathbb{Z}_q$. Suppose a distinguisher $D$ distinguishes LWE samples $(A, A s + e)$ with $m$ rows from uniform with advantage $\varepsilon$, uniformly over the secret. Then there is an algorithm that, given $\mathrm{poly}(n, q, 1/\varepsilon)$ LWE samples with an unknown secret $s$, recovers $s$ with high probability in time $\mathrm{poly}(n, q, 1/\varepsilon)$ times the running time of $D$. For coordinate $j$ and guess $g \in \mathbb{Z}_q$, a fresh sample $(A, b)$ is first re-randomized to secret $s + s'$ by $b \mapsto b + A s'$ for uniform $s'$, then transformed by adding a uniform vector $r$ to column $j$ of $A$ and $(g + s'_j) r$ to $b$. If $g = s_j$ the result is a fresh LWE sample with uniform matrix; if $g \ne s_j$ its error $e + (g - s_j) r$ is uniform, so the sample is uniform. Estimating $D$'s acceptance probability on both kinds of input identifies the correct guess.

## Proof sketch

The transformation preserves the uniform law of $A$ and turns the error into $e + (g - s_j)r$; since $q$ is prime and $g - s_j \ne 0$, multiplication by $g - s_j$ is a bijection, making the error uniform. Re-randomizing the secret makes the test valid for a worst-case secret, and Chernoff bounds over $\mathrm{poly}(1/\varepsilon)$ trials per guess distinguish the two acceptance rates; there are $n q$ guesses in total.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [LWE with uniform errors has zero advantage](lwe-with-uniform-error.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
