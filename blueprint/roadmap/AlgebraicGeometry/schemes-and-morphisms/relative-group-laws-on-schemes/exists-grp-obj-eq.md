# A relative group law determines a group scheme

Let $R$ be a commutative ring, $f : A \to \operatorname{Spec} R$ a morphism of schemes, and $G$ a relative group law on $A$ over $\operatorname{Spec} R$. There is a group object structure on $A$ in the category of schemes over $\operatorname{Spec} R$, with multiplication $m$, unit $e$ and inverse $\iota$, such that for every test scheme $t : T \to \operatorname{Spec} R$ and all points $a, b \in A(t)$:

- $m \circ (a, b) = a \cdot b$, the product of $a$ and $b$ under $G$,
- $e \circ (T \to \operatorname{Spec} R) = 1_t$, where $T \to \operatorname{Spec} R$ is the unique morphism from $t$ to the terminal object,
- $\iota \circ a = a^{-1}$, the inverse of $a$ under $G$.
