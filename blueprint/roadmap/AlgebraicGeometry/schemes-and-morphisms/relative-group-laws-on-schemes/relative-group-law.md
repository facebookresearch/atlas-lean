# Relative group law on a scheme

Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism. For a scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$, write $A(t)$ for the set of morphisms from $t$ to $f$ in the category of schemes over $\operatorname{Spec} R$, that is, morphisms $x : T \to A$ with $f \circ x = t$. A relative group law on $A$ over $\operatorname{Spec} R$ consists of, for every such test scheme $t : T \to \operatorname{Spec} R$,

- a multiplication $A(t) \times A(t) \to A(t)$, $(x,y) \mapsto x \cdot y$,
- an identity element $1_t \in A(t)$,
- an inversion $A(t) \to A(t)$, $x \mapsto x^{-1}$,

such that multiplication is associative, $1_t \cdot x = x$, $x \cdot 1_t = x$ and $x^{-1} \cdot x = 1_t$ for all $x, y, z \in A(t)$, and multiplication is natural in the test scheme: for every morphism $\psi : T' \to T$ with $t \circ \psi = t'$ and all $x, y \in A(t)$,

$$
(x \cdot y) \circ \psi = (x \circ \psi) \cdot (y \circ \psi) \quad \text{in } A(t').
$$
