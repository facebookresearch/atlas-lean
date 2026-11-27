# Correctness of counter mode

Let $N > 0$, let the key space $K$ be finite and nonempty, and let $Y$ be an additive commutative group. For every keyed function $F \colon K \to \mathbb{Z}/N \to Y$, [counter mode](ctr-scheme.md) with $\ell$-block messages is correct: for every key in the support of key generation, every message $m$ and every ciphertext in the support of the encryption of $m$, decryption returns `some` $m$.
