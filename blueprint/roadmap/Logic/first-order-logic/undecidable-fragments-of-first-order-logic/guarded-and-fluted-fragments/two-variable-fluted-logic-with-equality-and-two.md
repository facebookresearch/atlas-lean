# Two-variable fluted logic with equality and two transitive relations is undecidable

Satisfiability and finite satisfiability of two-variable fluted sentences with equality and two binary predicates interpreted as transitive relations are both undecidable.

**Theorem (Pratt-Hartmann and Tendera).** The problems $\mathrm{Sat}(\mathcal{FL}^2_=\,2\mathrm T)$ and $\mathrm{FinSat}(\mathcal{FL}^2_=\,2\mathrm T)$ are undecidable. That is, there is no algorithm that decides, for a sentence of the two-variable [fluted fragment](fluted-fragment.md) over a relational signature with ordinary predicates of arity at most $2$, with the equality atom $x_1 = x_2$ and with two distinguished binary predicates $T_1, T_2$, whether it has a model in which $T_1$ and $T_2$ are transitive; and none that decides whether it has such a finite model.

Both problems remain undecidable for sentences that also lie in the guarded fragment, and when one of the two transitive relations is required to be an equivalence relation, giving $\mathcal{FL}^2_=\,1\mathrm T1\mathrm E$ (Corollary 26 of the source). With only one transitive relation, $\mathcal{FL}^m_=\,1\mathrm T$ is decidable for all $m$ (Theorem 20 of the source); decidability of $\mathcal{FL}^m\,2\mathrm T$ without equality is left open there.

## Depends on

- [Fluted fragment](fluted-fragment.md)

## Proof depends on

None.

## Expansion

The proof builds a sentence $\varphi_{\mathrm{grid}}$ of $\mathcal{FL}^2_=\,2\mathrm T$ every model of which contains, in effect, a homomorphic embedding of the grid $\mathbb N^2$ (Lemma 24). For a tiling system $\mathcal C$ (finitely many tiles with horizontal and vertical adjacency constraints), a sentence $\eta_{\mathcal C}$ adds unary predicates for the tiles and the constraints. Then $\eta_{\mathcal C}$ is satisfiable iff $\mathcal C$ tiles $\mathbb N^2$, and finitely satisfiable iff $\mathcal C$ has a periodic tiling of $\mathbb N^2$. The set of tiling systems with a periodic tiling is recursively inseparable from the set of tiling systems with no tiling at all (Gurevich and Koryakov; Proposition 23 of the source), so no decidable set separates the finitely satisfiable $\eta_{\mathcal C}$ from the unsatisfiable ones; this makes both $\mathrm{Sat}$ and $\mathrm{FinSat}$ undecidable at once.

## Sources

- I. Pratt-Hartmann and L. Tendera, "The fluted fragment with transitive relations", *Annals of Pure and Applied Logic* 173(1), 2022, article 103042, <https://doi.org/10.1016/j.apal.2021.103042>; numbers from arXiv:2006.11169v1, <https://arxiv.org/abs/2006.11169v1>: Section 4.1: Lemma 24, Proposition 23, Theorem 25 and Corollary 26; Theorem 20.
- Y. Gurevich and I. O. Koryakov, "Remarks on Berger's paper on the domino problem", *Siberian Mathematical Journal* 13(2):319–321, 1972, <https://doi.org/10.1007/BF00971620>: the recursive inseparability used in the proof; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Proposition 23).
