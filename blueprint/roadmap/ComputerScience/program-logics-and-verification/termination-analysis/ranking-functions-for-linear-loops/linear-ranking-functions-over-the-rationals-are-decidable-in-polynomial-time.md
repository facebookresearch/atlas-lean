# Linear ranking functions over the rationals are decidable in polynomial time

The problem $\mathrm{LinRF}(\mathbb{Q})$, whether a rational multipath [linear-constraint loop](linear-constraint-loops.md) given by its constraints has a [linear ranking function](linear-ranking-functions.md), is decidable in polynomial time, and an LRF can be synthesized in polynomial time when one exists. The method of Podelski and Rybalchenko reduces the existence of an LRF for one transition polyhedron to the feasibility of a system of linear inequalities whose size is polynomial in that of the loop, and the LRFs of a multipath loop are those common to its paths. The problem remains in polynomial time when the polyhedra are given by generators instead of constraints.

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Proof depends on

- [Podelski–Rybalchenko certificates for linear ranking functions](podelski-rybalchenko-certificates-for-linear-ranking-functions.md)
- [Linear programming is in P (Khachiyan)](../../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 2.3 (statement that $\mathrm{LinRF}(\mathbb{Q})$ is decidable in polynomial time, with references to Podelski and Rybalchenko and to Mesnard and Serebrenik), Section 4.4, Theorem 4.20 (the Podelski–Rybalchenko constraints), Section 4.5, Lemma 4.23 and the paragraph before it (multipath loops), and the remark at the end of Section 3 (generator representation).
