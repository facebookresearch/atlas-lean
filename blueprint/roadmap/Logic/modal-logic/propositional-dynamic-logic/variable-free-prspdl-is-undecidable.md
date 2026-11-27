# Variable-free PRSPDL is undecidable

PDL with parallel composition remains undecidable when the input formulas contain no propositional variables at all, only the constant $\bot$.

**Theorem (Rybakov and Shkatov).** The variable-free fragment of [PRSPDL](pdl-with-parallel-composition-prspdl.md) over $\ast$-separated models is undecidable: no algorithm decides, for formulas built from $\bot$, $\to$, program boxes, atomic programs, the component programs $r_1, r_2, s_1, s_2$, tests, composition, parallel composition and iteration, whether they are valid (equivalently, whether their negations are satisfiable).

The same source shows that variable-free fragments do not lower complexity for regular PDL (EXPTIME-complete) or PDL with intersection (2EXPTIME-complete) either.

## Depends on

- [PDL with parallel composition (PRSPDL)](pdl-with-parallel-composition-prspdl.md)

## Proof depends on

None.

## Expansion

The proof embeds PRSPDL over $\ast$-separated models into its variable-free fragment (Theorem 3.9) and uses the undecidability of PRSPDL proved by Balbiani and Tinchev. The embedding first relativizes every box to a fresh variable $p_{n+1}$ and adds a conjunct $\Theta$ making $p_{n+1}$ closed under the programs occurring in the formula (PRSPDL has no choice, so $\Theta$ runs over all sequences of nested program terms); then each propositional variable is replaced by a variable-free formula that, in a suitably constructed model, is true exactly at the intended states, using atomic programs to attach distinguishable variable-free patterns to states.

## Sources

- M. Rybakov and D. Shkatov, "Complexity and expressivity of propositional dynamic logics with finitely many variables", *Logic Journal of the IGPL* 26(5):539–547, 2018, doi:10.1093/jigpal/jzy014; read as arXiv:1901.06407v1, <https://arxiv.org/abs/1901.06407v1>: Theorem 3.10 of arXiv:1901.06407v1, with Theorem 3.9 and the construction for IPDL it adapts.
