# Nearest-codeword decoding under radial noise: ties including the transmitted message succeed with probability one over the tie size

Let $E : M \to \mathbb{F}_2^n$ be an encoder of a finite message set, let the message $m$ be uniform, and let the received word be $y = E(m) + N$ with noise $N$ independent of $m$ and radial: $\Pr[N = z]$ depends only on the Hamming weight of $z$. Let $T(y)$ be the set of messages whose encodings are nearest to $y$ in Hamming distance, and $D$ any deterministic decoder that always outputs an element of $T(y)$. Then every element of $T(y)$ has the same joint probability with $y$, so conditional on receiving $y$ and on $m \in T(y)$ (when this event has positive probability) the decoder succeeds with probability exactly $1/|T(y)|$. In particular, at every noise weight, two-way ties including the transmitted message cause errors with exactly half of their probability, while ties excluding the transmitted message ($m \notin T(y)$) always cause errors.

## Proof sketch

The joint mass of $(y, m')$ is $|M|^{-1}\Pr[N = y + E(m')]$, which depends only on the distance from $y$ to $E(m')$; all nearest messages share that distance. The decoder outputs one fixed element of $T(y)$, which carries a $1/|T(y)|$ share of the conditional mass.

## Depends on

- [Error probability of maximum-likelihood decoding, ties counted as errors](../random-coding-bound-and-gallager-s-exponent/ml-error-prob.md)

## Sources

- C. Aguilar-Melchor, O. Blazy, J.-C. Deneuville, P. Gaborit and G. Zémor, "Efficient Encryption From Random Quasi-Cyclic Codes", IEEE Transactions on Information Theory 64(5), 2018.
- C. E. Shannon, "A Mathematical Theory of Communication", Bell System Technical Journal, 1948.
