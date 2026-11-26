# A difference-universal hash with a uniform offset is pairwise unpredictable

Let $H$ be $\varepsilon$-difference-universal into a finite abelian group $T$, and let $H'_{(k, u)}(m) = H_k(m) + u$ with $u$ uniform in $T$ and independent of $k$. Then $H'$ is $\varepsilon$-pairwise unpredictable: every two-stage adversary that obtains $H'(m)$ for one message $m$ of its choice and then outputs $(m', t')$ with $m' \ne m$ has $\Pr[H'(m') = t'] \le \varepsilon$.

## Proof sketch

The revealed value $H_k(m) + u$ is uniform and independent of $k$ because of $u$; predicting $H_k(m') + u$ from it amounts to predicting the difference $H_k(m') - H_k(m)$.

## Depends on

- [Game characterizations of universal and difference-universal hashing](game-characterizations-of-universal-hashing.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
