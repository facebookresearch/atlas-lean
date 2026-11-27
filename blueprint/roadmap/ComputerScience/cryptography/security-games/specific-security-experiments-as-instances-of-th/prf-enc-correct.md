# PRF-based encryption is correct

Let the key space $K$ and the randomness space $X$ be finite and nonempty, and let $Y$ be an additive commutative group. For every $F \colon K \to X \to Y$, the [PRF-based scheme](prf-enc.md) is correct: for every key in the support of key generation, every message $m$ and every ciphertext in the support of the encryption of $m$, decryption returns `some` $m$.
