# Cutting planes equal facelike stabbing planes

Cutting planes is polynomially equivalent to the subsystem of stabbing planes in which every query is facelike, meaning one of its two sides cuts the current polytope in the empty set or in a face.

A stabbing planes query $(ax \le b - 1,\ ax \ge b)$, with integer $a$ and $b$, at a node with polytope $P$ is **facelike** if one of the sets $P \cap \{x \in \mathbb{R}^n : ax \le b - 1\}$ and $P \cap \{x \in \mathbb{R}^n : ax \ge b\}$ is empty or a face of $P$. A stabbing planes refutation is **facelike** if all its queries are facelike.

**Theorem.** The proof systems cutting planes (CP) and facelike stabbing planes are polynomially equivalent.

## Expansion

Simulating CP by facelike SP is the standard simulation: each Chvátal-Gomory cut $ax \ge \lceil b \rceil$ is a query whose other side is empty. For the converse, walk the facelike SP tree bottom up. At a query, the side that is a face $P \cap \{ax = b'\}$ of $P$ is refuted by the subtree, and Schrijver's lemma lets a CP derivation from $P$ itself simulate a CP refutation of a face of $P$, deriving $ax \ge b' + 1$; combining with the other branch completes the derivation. This mirrors the Dadush-Tiwari quasi-polynomial CP refutations of Tseitin formulas, which were obtained through facelike SP refutations.

## Depends on

- [The stabbing planes proof system](../../stabbing-planes-and-semi-algebraic-branching/stabbing-planes-system.md)

## Proof depends on

- [Stabbing planes simulate cutting planes and equal tree-like R(CP)](../../stabbing-planes-and-semi-algebraic-branching/sp-simulates-cutting-planes.md)

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", *CCC 2021*, LIPIcs 200, doi:10.4230/LIPIcs.CCC.2021.6, arXiv:2102.05019 (arXiv version read: main characterization theorem in Section 1 and the definition of facelike queries in Section 3.1).
