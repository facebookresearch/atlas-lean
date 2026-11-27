# Cbc Mac Var Scheme

Let $K$ be a finite nonempty key type, $X$ an additive commutative group with decidable equality, and $E : K \to \mathrm{Perm}(X)$ a block cipher. Variable-length CBC-MAC on block lists $m \in X^{*}$ with tags in $X$ is the MAC scheme with

- key generation: $k$ uniform on $K$;
- tagging: deterministic, the point mass at the [list chaining](cbc-mac-list.md) of $m$ under $E_k$ (started at $0$, so the empty list is tagged $0$);
- verification: $(m, t)$ is accepted under $k$ iff $t$ equals that recomputed tag.

This scheme is insecure: see [Basic CBC-MAC is insecure for variable-length messages](mac-advantage-length-ext-forger.md).
