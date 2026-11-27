# One row of a Count-Sketch: unbiasedness and variance

A Count-Sketch row with $w$ buckets uses a seed $(\theta, \phi)$: a bucket hash $h_\theta : X \to [w]$ from a $1/w$-universal family and an independent sign hash $\epsilon(g_\phi(x)) \in \{\pm1\}$ from a pairwise independent family $g_\phi$ (uniform marginals) composed with a map $\epsilon$ that has mean $0$ on the range of $g$ and $\epsilon^2 = 1$, so the signs are pairwise independent and centered. For real weights $f : S \to \mathbb{R}$ on a finite set $S$, the estimate of $f(a)$ is $\epsilon(g_\phi(a))\sum_{x \in S,\, h_\theta(x) = h_\theta(a)} f(x)\epsilon(g_\phi(x))$. It is unbiased, its noise $\sum_{x \ne a,\, h_\theta(x) = h_\theta(a)} f(x)\epsilon(g_\phi(x))$ has second moment at most $\sum_{x \ne a} f(x)^2/w$, and by Chebyshev the noise exceeds $t$ in absolute value for at most a third of the seeds once $3\sum_{x\ne a}f(x)^2 \le wt^2$. Arbitrary real weights cover turnstile streams.

## Proof sketch

Pairwise independence of signs kills cross terms $\mathbb{E}\epsilon(g(x))\epsilon(g(x'))$ for $x \ne x'$, leaving $\sum_{x\ne a} f(x)^2\Pr[h(x) = h(a)] \le \sum_{x \ne a} f(x)^2/w$. Unbiasedness uses $\epsilon(g(a))^2 = 1$ and mean-zero signs for the other terms.

## Depends on

- [k-wise independent hash family](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)
- [Bounded universal hash functions](../../../cryptography/hash-functions/bounded-universal-hash-functions.md)

## Proof depends on

- [Chebyshev's inequality](../../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Sources

- M. Charikar, K. Chen and M. Farach-Colton, "Finding Frequent Items in Data Streams", Theoretical Computer Science 312(1), 2004.
- A. Chakrabarti, "Data Stream Algorithms: Lecture Notes", Dartmouth College, 2025.
