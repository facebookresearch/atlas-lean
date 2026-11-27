# Fixed-length CBC-MAC

Let $K$ be a finite nonempty key type, $X$ an additive commutative group with decidable equality, $\ell \in \mathbb{N}$, and $E : K \to \mathrm{Perm}(X)$ a block cipher. Fixed-length CBC-MAC on messages $m \in X^\ell$ with tags in $X$ is the MAC scheme with

- key generation: $k$ uniform on $K$;
- tagging: the point mass at the [basic CBC-MAC](cbc-mac.md) of $m$ under $E_k$ (started at $0$, folding $t \mapsto E_k(t + m_i)$);
- verification: $(m, t)$ is accepted under $k$ iff $t$ equals that recomputed tag.

At $\ell = 0$ every key tags the empty message with $0$. Katz and Lindell, 2nd ed., Construction 4.11, takes a positive length; the scheme here also covers $\ell = 0$.
