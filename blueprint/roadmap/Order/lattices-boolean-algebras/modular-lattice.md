# Modular lattice

A lattice is modular if, whenever $x \le z$, every $y$ satisfies $(x \vee y) \wedge z \le x \vee (y \wedge z)$.

Let $(L, \vee, \wedge)$ be a lattice: a partially ordered set in which every two elements $x, y$ have a least upper bound $x \vee y$ and a greatest lower bound $x \wedge y$. The lattice is *modular* if for all $x, y, z \in L$ with $x \le z$,

$$
(x \vee y) \wedge z \le x \vee (y \wedge z).
$$

The reverse inequality $x \vee (y \wedge z) \le (x \vee y) \wedge z$ holds in every lattice when $x \le z$, so a lattice is modular exactly when the modular law $x \vee (y \wedge z) = (x \vee y) \wedge z$ holds whenever $x \le z$; equivalently, it satisfies the identity $x \vee (y \wedge (x \vee z)) = (x \vee y) \wedge (x \vee z)$. Distributive lattices are modular, and so is the lattice of submodules of a module over a ring, in particular the lattice $\mathrm L(V)$ of subspaces of a vector space $V$ over a division ring, ordered by inclusion, with $U \vee W = U + W$ and $U \wedge W = U \cap W$.

## Sources

- Christian Herrmann, Yasuyuki Tsukamoto and Martin Ziegler, "On the consistency problem for modular lattices and related structures", *International Journal of Algebra and Computation* 26(8), 2016, pp. 1573–1595, doi:[10.1142/S0218196716500697](https://doi.org/10.1142/S0218196716500697); read as arXiv:1607.03315v1, <https://arxiv.org/abs/1607.03315v1>, whose numbering is used: Section 2 ("Algebraic structures") and Section 3 ("Coordinates in modular lattices").
