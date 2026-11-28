# Fragments of set theory with ordered pairs become undecidable with domain literals

The satisfiability problem for the quantifier-restricted fragment of set theory with ordered pairs studied by Cantone and Longo is decidable, but adding just two literals of the form x ⊆ dom(f), or of similar map-related forms, makes it undecidable.

**The language $\forall^\pi_{0,2}$.** Variables are of two sorts, set variables $x,y,z,\dots$ and map variables $f,g,h,\dots$; there is a binary pairing operator $[\cdot,\cdot]$, the predicates $\in$ and $=$, the Boolean connectives, and restricted quantifiers $(\forall x\in y)$, $(\exists x\in y)$, $(\forall[x,y]\in f)$, $(\exists[x,y]\in f)$. Atomic formulas are $x\in y$, $x=y$, $[x,y]\in f$ and $f=g$. A *prenex* formula is a block of restricted universal quantifiers, or a block of restricted existential quantifiers, followed by a quantifier-free formula; it is *simple* if no quantified variable occurs as the bound $z$ of another quantifier $(\forall x\in z)$. Formulas of $\forall^\pi_{0,2}$ are Boolean combinations of simple prenex formulas. Formulas are interpreted in the von Neumann universe of well-founded sets, with set variables denoting sets, map variables denoting sets of ordered pairs, and the pairing operator interpreted by a pairing function. A *normalized $\forall^\pi_{0,2}$-conjunction* is a conjunction of simple prenex formulas with universal prefixes; satisfiability of arbitrary $\forall^\pi_{0,2}$-formulas reduces to satisfiability of normalized conjunctions.

**Theorem (Cantone and Longo).** The satisfiability problem for normalized $\forall^\pi_{0,2}$-conjunctions extended with two positive literals of the form $x\subseteq\mathrm{dom}(f)$ is undecidable (Theorem 2 of the source). The same holds for normalized $\forall^\pi_{0,2}$-conjunctions extended with two literals of any one of the forms $x\subseteq\mathrm{range}(f)$, $h\subseteq f\circ g$ or $y\subseteq f[x]$, with $x,y$ set variables and $f,g,h$ map variables (Corollary 2).

Without these literals, the satisfiability problem for $\forall^\pi_{0,2}$ is decidable, in nondeterministic exponential time, and NP-complete for formulas whose quantifier prefixes have bounded length.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the domino problem: given a finite set of domino types with horizontal and vertical compatibility relations, is there a compatible tiling of the quadrant $\mathbb N\times\mathbb N$? It uses a set-theoretic variant of Peano systems: with two domain literals one can force a set to carry a successor map defined on all of it, yielding an infinite structure isomorphic to the natural numbers, and the universally quantified part of a normalized conjunction then describes the grid $\mathbb N\times\mathbb N$ through pairs and expresses the local compatibility conditions of the dominoes. A normalized conjunction with the two literals is satisfiable exactly when the domino system tiles the quadrant. The source derives the variants with range, composition and map image from this theorem, using the many set-theoretic constructs expressible in the language. The quadrant version of the tiling problem used here, tiling $\mathbb{N} \times \mathbb{N}$, is equivalent to the tiling problem for the plane on main by a compactness argument (a tile set tiles the quadrant iff it tiles arbitrarily large squares iff it tiles the plane); that equivalence has no page on main yet.

## Sources

- D. Cantone and C. Longo, "A decidable quantified fragment of set theory with ordered pairs and some undecidable extensions", in *Proceedings of the Third International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2012)*, Electronic Proceedings in Theoretical Computer Science 96, pp. 224–237, 2012, doi:[10.4204/EPTCS.96.17](https://doi.org/10.4204/EPTCS.96.17); read in arXiv:1210.2461v1 ([arXiv](https://arxiv.org/abs/1210.2461v1)): the syntax and semantics of $\forall^\pi_{0,2}$ in Section 3, normalized conjunctions, Theorem 1, Corollary 1 and Lemma 3 (decidability and complexity), and Definitions 1 (the domino problem) and 2 (Peano systems), Theorem 2 and Corollary 2 in Section 5 (Some undecidable extensions).
