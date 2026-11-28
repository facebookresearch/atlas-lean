# Strategy synthesis for global window L-PCTL with history-dependent randomized strategies is undecidable

Whether a Markov decision process has a history-dependent randomized strategy under which every history reachable from the initial state satisfies a bounded-horizon PCTL formula with linear probability constraints is undecidable: coRE-complete for flat non-strict formulas, and $\Sigma^1_1$-hard for flat formulas with strict inequalities.

**Setting (Bordais, Busatto-Gaston, Guha and Raskin).** $L$-PCTL extends [PCTL](../pctl.md) by linear constraints between probabilities: state formulas are built from literals $p$, $\neg p$ with $\wedge$, $\vee$ and inequalities $\sum_{i=1}^n c_i \Pr(\varphi_i) \succcurlyeq c_0$ with integer $c_i$ and ${\succcurlyeq} \in \{\geq, >\}$, and path formulas are $\mathbf{X}^{\ell}\Phi$ with $\ell \in \mathbb{N}$ and $\Phi_1 \mathbf{U}^{\ell} \Phi_2$, $\Phi_1 \mathbf{W}^{\ell} \Phi_2$ with $\ell \in \mathbb{N} \cup \{\infty\}$ (Definition 5). A *window formula* uses only finite horizons $\ell$ (encoded in unary); it is *flat* if probability operators are not nested and *non-strict* if every inequality uses $\geq$. A *global window formula* $\forall\mathbf{G}\,\Phi$, with $\Phi$ a window formula, holds in a state of a Markov chain when every state reachable from it satisfies $\Phi$; the states of the induced chain $M[\sigma]$ are the finite histories of $M$, so under a history-dependent strategy the condition ranges over histories. The *synthesis problem* asks, given a finite [Markov decision process](../markov-decision-processes-and-adversaries.md) $M$, whose probabilities are rational numbers written as pairs of integers in binary, and a formula, whether some strategy $\sigma$, history-dependent and randomized unless restricted, makes the induced Markov chain $M[\sigma]$ satisfy the formula at its initial state (Definition 6).

**Theorem (Bordais, Busatto-Gaston, Guha and Raskin).** The synthesis problem for flat, non-strict global window $L$-PCTL formulas is in coRE (Theorem 24 of arXiv:2204.14107v1) and coRE-hard (Theorem 37), hence undecidable.

With strict inequalities allowed, the synthesis problem for flat global window $L$-PCTL formulas is even $\Sigma^1_1$-hard (Theorem 38 of arXiv:2204.14107v1), by a reduction from [recurring computations of two-counter machines](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md). Restricted to deterministic strategies the problem is decidable: NP-complete for memoryless deterministic strategies and in 2EXPTIME for history-dependent deterministic ones; for memoryless randomized strategies it is in PSPACE. Synthesis for full PCTL with history-dependent deterministic strategies was known to be $\Sigma^1_1$-complete (Brázdil, Brožek, Forejt and Kučera), as the source recalls.

## Depends on

- [PCTL](../pctl.md)
- [Markov decision processes and adversaries](../markov-decision-processes-and-adversaries.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The coRE-hardness reduces from non-halting of two-counter Minsky machines: counter values $(x_2, x_3)$ are stored in the probability $\frac{5}{6} \cdot 2^{-x_2} \cdot 3^{-x_3}$, chosen by the strategy, of seeing a predicate within a few steps, and gadgets for increment, decrement, zero test and halting, chained by entering and exiting probabilities, let a strategy satisfy the formula exactly when the machine runs forever; membership in coRE comes from a fixpoint characterization in Section 3 of the source. For the $\Sigma^1_1$-hardness, strict inequalities let the strategy announce how many steps until the first instruction recurs, stored in an extra counter that must not reach $0$, which reduces from the existence of a computation visiting the first instruction infinitely often. A complete expansion links a page for the coRE-completeness of non-halting of two-counter machines.

## Sources

- B. Bordais, D. Busatto-Gaston, S. Guha and J.-F. Raskin, "Strategy Synthesis for Global Window PCTL", in *49th International Colloquium on Automata, Languages, and Programming (ICALP 2022)*, Leibniz International Proceedings in Informatics 229, Schloss Dagstuhl, 2022, pp. 115:1–115:20, doi:[10.4230/LIPIcs.ICALP.2022.115](https://doi.org/10.4230/LIPIcs.ICALP.2022.115); read as arXiv:2204.14107v1 ([arXiv](https://arxiv.org/abs/2204.14107v1)), whose numbering is used (one global counter): the definitions of Section 2, the results table of the introduction, Theorem 24 of Section 3, and Theorems 37 and 38 of Section 4.
