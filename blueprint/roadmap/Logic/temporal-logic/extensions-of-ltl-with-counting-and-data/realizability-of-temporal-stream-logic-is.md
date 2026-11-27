# Realizability of temporal stream logic is undecidable

Temporal stream logic extends LTL with updates of cells by uninterpreted function terms and with uninterpreted predicate terms; deciding whether a specification in this logic can be realized by a reactive system, for all interpretations of its function and predicate symbols, is undecidable.

**Setting.** Temporal stream logic (TSL) is defined on the page [temporal stream logic modulo theories](temporal-stream-logic-modulo-theories.md): its formulas are built from predicate terms and updates $[\![c\leftarrow\tau_f]\!]$ of cells $c$ by function terms $\tau_f$, using the LTL connectives $\neg$, $\wedge$, $\mathbf X$ and $\mathbf U$. Cells are split into input signals and output cells. A strategy reads the history of inputs and chooses at each step an update for every output cell; a run then assigns to each cell, at each time, a term built from the function symbols. The *realizability problem* asks, given a TSL formula $\varphi$, whether there is a strategy $\sigma$ such that for every input sequence $\iota$ and every interpretation of the function and predicate symbols, the run of $\sigma$ on $\iota$ satisfies $\varphi$.

**Theorem (Finkbeiner, Klein, Piskac and Santolucito).** The realizability problem of TSL is undecidable.

The proof uses no input signals, so satisfiability of TSL in the sense of the source, the existence of a run satisfying the formula under every interpretation, is undecidable as well. Realizability is approximated soundly by translating TSL into LTL and refining the approximation by counterexample-guided abstraction refinement.

## Depends on

- [Temporal stream logic modulo theories](temporal-stream-logic-modulo-theories.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem. Given words $w_0,\dots,w_n$ and $v_0,\dots,v_n$ over an alphabet $\Sigma$, fix a unary function symbol for every letter of $\Sigma$, a constant $X$, a unary predicate $p$, and two output cells $A$ and $B$ with no inputs. Initially both cells are set to $X$; in every later step the system picks an index $j$ and applies to $A$ the composition of the letter functions of $w_j$ and to $B$ that of $v_j$. The formula requires that eventually $p(A)\leftrightarrow p(B)$ holds for the universally quantified predicate $p$, which, ranging over all interpretations, forces the two terms built in $A$ and $B$ to coincide syntactically. A strategy realizing the formula exists exactly when the correspondence instance has a solution.

## Sources

- B. Finkbeiner, F. Klein, R. Piskac and M. Santolucito, "Temporal stream logic: synthesis beyond the bools", in *Computer Aided Verification (CAV 2019)*, Lecture Notes in Computer Science 11561, pp. 609–629, Springer, 2019, doi:[10.1007/978-3-030-25540-4_35](https://doi.org/10.1007/978-3-030-25540-4_35); read in arXiv:1712.00246v2 ([arXiv](https://arxiv.org/abs/1712.00246v2)): the definition of the realizability problem in the appendix on the semantics of TSL, the undecidability theorem with its proof sketch and the remark after it, and the detailed proof in the appendix.
