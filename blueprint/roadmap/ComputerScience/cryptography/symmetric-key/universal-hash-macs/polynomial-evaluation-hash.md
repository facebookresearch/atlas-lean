# Polynomial-evaluation hashing is almost $\Delta$-universal

Let $\mathbb{F}$ be a finite field. Hash a message $m = (m_1, \dots, m_{\ell'-1}) \in \mathbb{F}^{<\ell}$ with key $k \in \mathbb{F}$ by appending a field element $m_{\ell'}$ encoding its length and evaluating

$$
H(k, m) = m_1 k^{\ell'} + m_2 k^{\ell' - 1} + \cdots + m_{\ell'} k .
$$

If the length encoding is injective, $H$ is $\ell/|\mathbb{F}|$-almost-$\Delta$-universal on messages of length less than $\ell$. The variant that aligns messages to a fixed top degree, $m_1 k^\ell + \dots + m_{\ell'}k^{\ell - \ell' + 1}$, is also $\ell/|\mathbb{F}|$-AXU when no positive length is encoded as $0$, but fails to be almost universal if the length $1$ is encoded as $0$ and $\ell \ge 2$ (the empty message and a one-block message collide under every key). Instantiated in Carter–Wegman MACs, these hashes give one-time, counter-based, nonce-based and randomized MACs for variable-length messages with forgery bound $\ell/|\mathbb{F}|$ per attempt.

## Proof sketch

For distinct messages the difference $H(k, m) - H(k, m') - \delta$ is a nonzero polynomial in $k$ of degree at most $\ell$ (nonzero because of the injective length block), which has at most $\ell$ roots.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](delta-universal-hash-families.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
