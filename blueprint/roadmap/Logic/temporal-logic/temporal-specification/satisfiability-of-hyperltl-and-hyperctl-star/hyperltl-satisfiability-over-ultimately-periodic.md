# HyperLTL satisfiability over ultimately periodic traces is Σ¹₁-complete

Whether a HyperLTL sentence has a model consisting of ultimately periodic traces only is still a $\Sigma^1_1$-complete problem, so restricting models to individually finite-state traces does not lower the complexity of satisfiability.

**Theorem (Fortin, Kuijer, Totzke and Zimmermann).** Fix a finite set $AP$ of atomic propositions. A trace $t \in (2^{AP})^\omega$ is *ultimately periodic* if $t = x\cdot y^\omega$ for some nonempty finite words $x, y$ over $2^{AP}$. The problem asking, given a [HyperLTL](../hyperltl.md) sentence $\varphi$ over $AP$, whether some set $T$ of ultimately periodic traces (finite or infinite) satisfies $\varphi$, is $\Sigma^1_1$-complete (Theorem 3.4 of the source).

Here $\Sigma^1_1$ is the class of sets of natural numbers definable by an arithmetic formula preceded by a block of existential quantifiers over functions $\mathbb N \to \mathbb N$, as on the page [HyperLTL satisfiability is Σ¹₁-complete](hyperltl-satisfiability-is-sigma-1-1-complete.md). The set $T$ is not required to be finite: for finite sets of ultimately periodic traces the problem is $\Sigma^0_1$-complete (Finkbeiner, Hahn and Hans, recalled after Theorem 3.1 of the source), and satisfiability by a finite transition system (finite-state satisfiability) is $\Sigma^0_1$-complete (Proposition 3.5, attributed to Finkbeiner, Rabe and Sánchez and to Finkbeiner and Hahn).

## Depends on

- [HyperLTL](../hyperltl.md)
- [Ultimately periodic sequences](../../../../Dynamics/topological-symbolic-dynamics/eventually-periodic-sequences/is-ultimately-periodic.md)
- [HyperLTL satisfiability is Σ¹₁-complete](hyperltl-satisfiability-is-sigma-1-1-complete.md)

## Proof depends on

None.

## Expansion

The lower bound reduces from a variant of the recurring tiling problem that Harel showed $\Sigma^1_1$-complete: tile the part $\{(i, j) \in \mathbb N^2 \mid i \ge j\}$ of the quadrant below the diagonal so that a designated tile $\tau_0$ occurs in every row. The encoding is the one used for general satisfiability, with columns as traces and rows as time points, modified so that every time point after the column marker $x$ carries a special "null" tile (which makes each trace ultimately periodic), the matching constraints are checked only up to the marker, and for every trace there is a trace carrying $\tau_0$ at the time of its marker. Membership in $\Sigma^1_1$ follows as for general satisfiability, from the existence of countable models coded by functions on $\mathbb N$. A good expansion adds a page for the $\Sigma^1_1$-completeness of Harel's variant of the recurring tiling problem below the diagonal.

## Sources

- M. Fortin, L. B. Kuijer, P. Totzke and M. Zimmermann, "HyperLTL Satisfiability Is Highly Undecidable, HyperCTL* is Even Harder", *Logical Methods in Computer Science* 21(1), 2025, article 3, <https://doi.org/10.46298/lmcs-21(1:3)2025>; numbers from arXiv:2303.16699v5, <https://arxiv.org/abs/2303.16699v5>: Theorem 3.4 and its proof, the remark after Theorem 3.1 (finite sets of ultimately periodic traces) and Proposition 3.5 (finite-state satisfiability).
- D. Harel, "Recurring dominoes: making the highly undecidable highly understandable", *North-Holland Mathematics Studies* 102:51–71, 1985, <https://doi.org/10.1016/S0304-0208(08)73075-5>: the $\Sigma^1_1$-complete tiling problem used for the lower bound; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (proof of Theorem 3.4).
