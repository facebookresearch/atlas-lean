# The isomorphism problem is undecidable for finitely presented groups with quadratic Dehn function

No algorithm decides whether two finitely presented groups with quadratic Dehn function are isomorphic; there is even a fixed such group $\bar G$ for which isomorphism with $\bar G$ is undecidable.

The isomorphism problem is undecidable within the class of finitely presented groups with quadratic Dehn function. Here, for a finite presentation $\langle A \mid R \rangle$, the Dehn function $f(n)$ is the least non-decreasing function such that every word of length at most $n$ representing $1$ is freely equal to a product of at most $f(n)$ conjugates of relators and their inverses; it is quadratic when it is bounded above and below by quadratic functions up to the usual equivalence ($f \preceq g$ if $f(n) \le C g(Cn) + Cn$ for some $C$). Let $QD$ be the class of finitely presented groups with quadratic Dehn function. The isomorphism problem in $QD$ is undecidable; moreover there is a group $\bar G \in QD$ such that no algorithm decides, for a finite presentation of a group $G \in QD$, whether $G \cong \bar G$ (Theorem 1.1 of the source).

By contrast, the isomorphism problem is solvable for hyperbolic groups (Sela; Dahmani and Guirardel), which are exactly the finitely presented groups with linear Dehn function, so linear is the only Dehn function bound that makes the problem solvable.

## Depends on

- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof builds on the authors' construction of finitely presented groups with quadratic Dehn function from $S$-machines, as in their group with quadratic Dehn function and undecidable conjugacy problem. Starting from a Turing machine $M_0$ whose language of accepted input words is not recursive, the source builds finitely presented groups $G_k$ with quadratic Dehn function, one for each input word $\alpha_k$, such that $G_k$ is isomorphic to a fixed group $\bar G$ exactly when $M_0$ accepts $\alpha_k$ (Lemma 4.10 and the proof of Theorem 1.1). A good expansion links pages for the $S$-machine construction and its lemmas.

## Sources

- A. Yu. Olshanskii and M. V. Sapir, "Algorithmic problems in groups with quadratic Dehn function", Groups, Geometry, and Dynamics 16 (2022), no. 4, 1289–1339, https://doi.org/10.4171/GGD/694; read in arXiv:2012.10417v1 (Theorem 1.1, its proof and Lemma 4.10 of arXiv:2012.10417v1).
