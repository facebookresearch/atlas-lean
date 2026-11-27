# Orbit-finite systems of linear inequalities

An orbit-finite system of linear inequalities has rows and unknowns indexed by orbit-finite sets with atoms: infinitely many inequalities and unknowns, but only finitely many up to renaming atoms. Solutions are finitely supported vectors, and finitary solutions have finitely many non-zero entries.

**Atoms.** Fix a countably infinite set $\mathbb{A}$ of atoms with no structure but equality (equality atoms), and let $\mathrm{Aut}$ be the group of all permutations of $\mathbb{A}$, acting on sets with atoms by renaming. A finite $T \subseteq \mathbb{A}$ *supports* a set $X$ if $\pi(X) = X$ for every $\pi \in \mathrm{Aut}$ fixing $T$ pointwise; $X$ is *finitely supported* if some finite $T$ supports it, and *equivariant* if $\emptyset$ does. A finitely supported set is *orbit-finite* if it is a finite union of orbits under the $T$-automorphisms for some finite support $T$ (for example $\mathbb{A}$, $\mathbb{A}^2$, or the set of $n$-tuples of distinct atoms). The *atom dimension* of an orbit is the size of the support of its elements.

**Vectors.** For an orbit-finite set $B$, a *vector* over $B$ is a finitely supported function $\vec{v} : B \to \mathbb{R}$; it is an *integer* vector if its values are integers, and *finitary* if $\vec{v}(b) \ne 0$ for only finitely many $b$. The inner product $\langle \vec{x}, \vec{y} \rangle = \sum_{b \in B} \vec{x}(b)\vec{y}(b)$ is defined when only finitely many terms are non-zero.

**Definition (Ghosh, Hofman and Lasota).** Let $B$ and $C$ be orbit-finite sets. An *orbit-finite system of linear inequalities* with row index $B$ and column index (unknowns) $C$ is a pair $(\vec{A}, \vec{t})$ of a finitely supported integer matrix $\vec{A} : B \times C \to \mathbb{Z}$ and a finitely supported integer target $\vec{t} : B \to \mathbb{Z}$. A vector $\vec{x}$ over $C$ is a *solution* if for every $b \in B$ the inner product $\langle \vec{A}(b, \cdot), \vec{x} \rangle$ is defined and

$$
\langle \vec{A}(b, \cdot), \vec{x} \rangle \ge \vec{t}(b).
$$

It is a $\mathbb{Z}$-solution if it is an integer vector. The decision problem $\mathrm{FinIneqSolv}(\mathbb{F})$, for $\mathbb{F} \in \{\mathbb{R}, \mathbb{Z}\}$, asks whether a given orbit-finite system has a finitary $\mathbb{F}$-solution; for the same $\mathbb{F}$ it is inter-reducible with the variant that asks for an arbitrary (finitely supported) $\mathbb{F}$-solution and with nonnegative $\mathbb{F}$-solvability of orbit-finite systems of equations, but not with finitary nonnegative solvability of equations, which is decidable for both $\mathbb{R}$ and $\mathbb{Z}$ (Theorem 20 of the arXiv version).

## Depends on

- [Nominal set](../../programming-language-semantics/nominal-sets/nominal-set.md)

## Proof depends on

None.

## Expansion

Orbit-finite sets are finitely representable, which makes these systems legitimate inputs to algorithms. Restricting to finitary or to integer solutions changes solvability: there are systems with real but no finitary real solutions, and the real problem is decidable (in exponential time, and polynomial time for fixed atom dimension) while the integer problem is not.

## Sources

- Arka Ghosh, Piotr Hofman and Sławomir Lasota, "Orbit-finite Linear Programming", Journal of the ACM 72(1), 39 pages, 2025, <https://doi.org/10.1145/3703909>; Sections 2 and 3, Definition 11 and Theorem 17 of arXiv:2302.00802v4, <https://arxiv.org/abs/2302.00802v4>.
- Arka Ghosh, Piotr Hofman and Sławomir Lasota, "Orbit-finite linear programming", 38th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2023), pp. 1–14, 2023, <https://doi.org/10.1109/LICS56636.2023.10175799>; conference version, not read (the statements rest on the version read of the first source above).
