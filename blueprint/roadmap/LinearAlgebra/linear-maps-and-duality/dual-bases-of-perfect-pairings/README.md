# Dual basis of a perfect pairing

Let $A$ be a commutative ring and $B : M \times N \to A$ a perfect pairing of $A$-modules: $B$ is bilinear, and $x \mapsto B(x, \cdot)$ and $y \mapsto B(\cdot, y)$ are linear isomorphisms $M \to N^*$ and $N \to M^*$. Let $(b_i)_{i \in \iota}$ be a basis of $N$ indexed by a finite set. The dual basis of $(b_i)$ with respect to $B$ is the basis $(b_i^\vee)$ of $M$ whose $i$-th vector is the preimage, under the isomorphism $x \mapsto B(x, \cdot)$, of the $i$-th coordinate functional $b_i^*$ of $(b_i)$, where $b_i^*(b_j) = 1$ if $i = j$ and $0$ otherwise.

## Idea

For the dot product on $\mathbb{R}^n$, the dual basis of a basis $(b_i)$ is the basis $(b_i^\vee)$ with $b_i^\vee \cdot b_j = \delta_{ij}$: its vectors are the rows of the inverse of the matrix whose columns are the $b_j$. A perfect pairing is the general setting in which this works: it identifies $M$ with the dual of $N$, and the dual basis is the image of the coordinate functionals. So $B(b_i^\vee, b_j) = 1$ if $i = j$ and $0$ otherwise, and this property characterizes the dual basis; every $x \in M$ is recovered from its pairings with the $b_j$ as $x = \sum_j B(x, b_j)\, b_j^\vee$. Examples are the trace form of a finite separable field extension, which gives the dual basis used to define the different, and the reciprocal lattice of a crystal.

## Statements

- [Dual basis with respect to a perfect pairing](dual-basis.md)
- [Evaluation of the dual basis](dual-basis-apply.md): the evaluation formula $B(b_i^\vee, b_j) = \delta_{ij}$
- [Existence of a dual basis for a perfect pairing](exists-dual-basis.md): existence
- [Uniqueness of the dual basis](eq-dual-basis-of.md): uniqueness
- [Existence and uniqueness of the dual basis for a perfect pairing](exists-unique-dual-basis.md): existence and uniqueness together
