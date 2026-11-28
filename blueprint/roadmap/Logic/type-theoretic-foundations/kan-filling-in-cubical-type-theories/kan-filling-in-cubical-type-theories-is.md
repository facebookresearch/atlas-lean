# Kan filling in cubical type theories is undecidable

Deciding whether a cube with a prescribed boundary can be built from the cells of a context using contortions and iterated Kan filling is undecidable, because the word problem of any finitely presented group reduces to it.

**Setting.** In the cubical type theories considered by the source, a *context* $\Gamma$ is a collection of cells, each an $n$-dimensional cube with prescribed faces, and terms in dimension variables $\Psi$ are built from the cells of $\Gamma$ by *contortions* (reindexings of cubes by maps of the interval, for any of the cartesian, disjunctive, Dedekind or De Morgan sublanguages) and by the *filling operator*, which fills an open box of cells to a cube. *Kan cells* are the terms built by iterated applications of the filling operator to contorted cells. A *Kan boundary* $\phi$ in $\Gamma$ and $\Psi$ prescribes compatible faces of a cube; the problem $\mathrm{Kan}(\Gamma,\Psi,\phi)$ asks whether there is a Kan cell $t$ in $\Gamma$ and $\Psi$ with boundary $\phi$.

**Theorem (Doré, Cavallo and Mörtberg).** $\mathrm{Kan}$ is undecidable (Theorem 3.23 of the source). More specifically, there are contexts $\Gamma$ for which no algorithm decides the problem for two-dimensional Kan boundaries in $\Gamma$, uniformly in the boundary.

The result holds whichever sublanguage of contortions is used. The source instead gives a solver for the contortion problem, filling boundaries by contortions alone, for Dedekind and De Morgan contortions, and heuristics for Kan solving that work on practical examples.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Every finitely presented group has a *convenient presentation*, with all relations of the form $abc^{-1}=1$. For such a presentation $\langle X\mid R\rangle$ of a group $G$, let $\Gamma$ consist of a point $\star$, a loop $\hat a$ at $\star$ for each generator $a\in X$, and for each relation $abc^{-1}=1$ a square $s_{a,b,c}$ with sides $\hat a$, $\hat b$, $\hat c$ and $\star$. Words $v,w$ over $X$ become composite paths $\hat v,\hat w$, and an interpretation of Kan cells as elements of $G$ shows that there is a square with constant vertical sides at $\star$, bottom $\hat v$ and top $\hat w$ if and only if $v=w$ in $G$. Since there are finitely presented groups with undecidable word problem, the problem for the corresponding context is undecidable.

## Sources

- M. Doré, E. Cavallo and A. Mörtberg, "Automating boundary filling in cubical type theories", *Logical Methods in Computer Science* 22(2), paper 28, 2026, doi:[10.46298/lmcs-22(2:28)2026](https://doi.org/10.46298/lmcs-22(2:28)2026); read in arXiv:2402.12169v5 ([arXiv](https://arxiv.org/abs/2402.12169v5)): Definition 2.12 (Kan cells), Problem 3.7 ($\mathrm{Kan}$), Definition 3.8 and Proposition 3.9 (convenient presentations), Definition 3.11 (the context built from a presentation), Corollary 3.22 (fillable squares and equality of words), and Theorem 3.23 with its proof.
