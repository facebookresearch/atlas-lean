# Nonce-based and randomized Carter–Wegman MACs

Let $H$ be $\varepsilon$-AXU into $Y$ and $F : K' \times \mathcal{N} \to Y$ a pseudorandom function. (i) The *nonce-based* Carter–Wegman MAC tags $(m, \nu)$ with a never-repeated nonce $\nu$ as $(\nu, H(k, m) + F(k', \nu))$. For every forger making $Q$ tagging queries with distinct nonces, the probability of a strong forgery is at most $\max(\varepsilon, 1/|Y|)$ plus the PRF advantage of an explicit reduction. (ii) The *randomized* variant draws $\nu$ uniformly from $\mathcal{N}$ for each tag; then the forgery probability is at most $Q^2/(2|\mathcal{N}|)$ (nonce collisions) plus $\max(\varepsilon, 1/|Y|)$ plus the PRF advantage.

## Proof sketch

Replace $F(k', \cdot)$ by a random function: each pad at a fresh nonce is uniform, so the tagging oracle can be simulated exactly, and a forgery at a used nonce requires predicting a hash difference ($\le \varepsilon$) while one at a fresh nonce requires guessing a uniform pad ($\le 1/|Y|$). In the randomized variant, condition on no nonce collision.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](delta-universal-hash-families.md)
- [The MAC forgery experiment](../pseudorandom-functions/mac-game.md)
- [Polynomial-query unforgeability of MACs](../../security-games/asymptotic-security/poly-query-macsecure.md)

## Proof depends on

- [One-time and multi-query security of Carter–Wegman MACs](carter-wegman-mac-security.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Mark N. Wegman and J. Lawrence Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
