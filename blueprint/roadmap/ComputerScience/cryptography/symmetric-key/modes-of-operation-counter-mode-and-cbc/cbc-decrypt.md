# CBC decryption

Let $X$ be an additive commutative group and let $p' \colon X \to X$ be any function. CBC decryption of a ciphertext $(\mathrm{iv}, c)$ with $c \in X^\ell$ is the [unchaining](cbc-unchain.md) of $c$ from $\mathrm{iv}$ with $p'$. In [CBC mode](cbc-scheme.md) it is instantiated with the inverse permutation of the block cipher; the definition itself does not require $p'$ to be an inverse.
