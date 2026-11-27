# The extension of an isomorphism commutes with the factorizations

Let $C$ be a symmetric monoidal category with a symmetric trace $T$, let $\mathrm{Int}(T)$ be its [Int construction](../the-int-construction/README.md), whose objects are pairs $X = (X^+, X^-)$ of objects of $C$, and let $J : C \to \mathrm{Int}(T)$, $J(A) = (A, \mathbf{1})$, be the embedding. Let $D$ be a right rigid symmetric monoidal category, and let $F, G : C \to D$ be braided strong monoidal functors that preserve $T$, sending it to the [canonical trace](../symmetric-traces-and-dual-comparisons/symmetric-trace-of-rigid.md) of $D$, with [canonical extensions](extend.md) $\operatorname{ext}(F)$ and $\operatorname{ext}(G)$ and [factorization isomorphisms](extension-iso.md) $\varphi_F : \operatorname{ext}(F) \circ J \cong F$ and $\varphi_G : \operatorname{ext}(G) \circ J \cong G$. Let $i : F \cong G$ be a monoidal natural isomorphism. For every object $A$ of $C$,

$$\varphi_{G,A} \circ \operatorname{ext}(i)_{J(A)} = i_A \circ \varphi_{F,A}:$$

the [extension](extend-iso.md) of $i$ at $J(A)$ followed by the factorization for $G$ equals the factorization for $F$ followed by $i$ at $A$. Equivalently, as natural isomorphisms $\operatorname{ext}(F) \circ J \cong G$, the restriction of $\operatorname{ext}(i)$ along $J$ followed by $\varphi_G$ equals $\varphi_F$ followed by $i$.
