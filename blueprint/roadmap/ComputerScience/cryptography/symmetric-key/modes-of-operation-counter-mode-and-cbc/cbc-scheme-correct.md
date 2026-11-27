# Correctness of CBC mode

Let the key space $K$ and the block space $X$ be finite and nonempty, and let $X$ be an additive commutative group. For every block cipher $E$, [CBC mode](cbc-scheme.md) with $\ell$-block messages is correct: for every key in the support of key generation, every message $m$ and every ciphertext in the support of the encryption of $m$, decryption returns `some` $m$. This uses only that $E_k^{-1}$ inverts $E_k$; it is not a pseudorandomness assumption.
