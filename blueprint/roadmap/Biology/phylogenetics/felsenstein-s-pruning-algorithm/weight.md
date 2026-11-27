# Weight of a tree labeling

Let $R$ be a commutative semiring and $\mathrm{obs} : L \times S \to R$ leaf weights (the observed data at one site). The weight of a [labeling](labeling.md) $z$ of a [tree](tree.md) $t$ given root state $s$ is defined recursively:

- for a leaf $l$: $W(l, s) = \mathrm{obs}(l, s)$;
- for an internal node with weights $P, Q$ and children $l, r$, where $z$ gives the states $a$ to $l$ and $b$ to $r$ and labelings $z_l, z_r$:

$$W(t, s, z) = P(s, a)\, W(l, a, z_l) \cdot Q(s, b)\, W(r, b, z_r).$$
