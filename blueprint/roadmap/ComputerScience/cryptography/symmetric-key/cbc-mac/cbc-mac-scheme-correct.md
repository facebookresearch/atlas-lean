# Correctness of fixed-length CBC-MAC

Let $K$ be a finite nonempty key type, $X$ an additive commutative group with decidable equality, $\ell \in \mathbb{N}$ (including $\ell = 0$) and $E : K \to \mathrm{Perm}(X)$ a block cipher. [Fixed-length CBC-MAC](cbc-mac-scheme.md) is correct: for every key $k$ in the support of key generation, every message $m \in X^\ell$ and every tag $t$ in the support of honest tagging of $m$ under $k$, verification accepts $(m, t)$ under $k$. Since tagging is deterministic, the only such $t$ is the recomputed tag, which verification compares against.
