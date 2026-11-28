# Bilinear group interfaces

A bilinear group interface consists of an integer $q > 1$, three commutative groups $G_1$, $G_2$ and $G_T$, group isomorphisms

$$\phi_1 : \mathbb{Z}/q\mathbb{Z} \to G_1, \qquad \phi_2 : \mathbb{Z}/q\mathbb{Z} \to G_2, \qquad \phi_T : \mathbb{Z}/q\mathbb{Z} \to G_T$$

from the additive group of residues modulo $q$, written multiplicatively in the targets, and a map $e : G_1 \times G_2 \to G_T$, the pairing, such that

$$e(\phi_1(a), \phi_2(b)) = \phi_T(ab) \qquad \text{for all } a, b \in \mathbb{Z}/q\mathbb{Z}.$$

So $G_1$, $G_2$ and $G_T$ are cyclic of order $q$, and on exponents the pairing is multiplication of residues. Bilinearity, the power law and nondegeneracy are consequences of these data, not further axioms. The isomorphisms are part of the data, so their inverses compute discrete logarithms in all three groups.
