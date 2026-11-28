# Reactive synthesis for MITL is undecidable, already on finite words

Synthesizing a controller for a timed plant so that every finite behavior satisfies a metric interval temporal logic formula is undecidable, and remains so for controllers with bounded clocks or bounded precision and for small fragments of MITL, on finite and on infinite timed words.

**Timed games and synthesis.** The alphabet is split into controllable actions $\Sigma_C$ and environment actions $\Sigma_E$. A *plant* is a timed automaton over $\Sigma_C\uplus\Sigma_E$; a controller proposes controllable actions with delays, the environment may preempt them with its own actions, and the outcome of a strategy is the set of timed words consistent with the strategy and the plant. For a specification formalism $\mathcal F$, $s\in\{u,d\}$ and $b\in\{\star,\omega\}$, the *reactive synthesis problem* $\mathrm{RS}^b_s(\mathcal F)$ asks, given a specification $S\in\mathcal F$ and a plant, both interpreted over finite timed words if $b=\star$ and infinite ones if $b=\omega$, whether the controller has a strategy all of whose outcomes lie in the timed language $L(S)$ when $s=d$ (desired behaviors), or outside it when $s=u$ (undesired behaviors). Restricted variants require the strategy to be implementable by a symbolic transition system: $\mathrm{IRS}$ (any such implementation), $\mathrm{BPrecRS}$ (bounded precision of the clock constraints) and $\mathrm{BClockRS}$ (a bounded number of clocks). Metric interval temporal logic (MITL) is the timed extension of LTL whose until operators carry non-singular time intervals.

**Theorem (Brihaye, Estiévenart, Geeraerts, Ho, Monmege and Sznajder).** $\mathrm{RS}^\star_d(\mathrm{MITL})$ is undecidable: reactive synthesis for MITL specifications of desired behaviors is undecidable on finite timed words (Theorem 1 of the source).

From this core result the source derives that $\mathrm{RS}^b_s(L)$, $\mathrm{IRS}^b_s(L)$, $\mathrm{BPrecRS}^b_s(L)$ and $\mathrm{BClockRS}^b_s(L)$ are undecidable for every $s\in\{u,d\}$ and $b\in\{\star,\omega\}$, where $L$ is either of the fragments $\mathsf{Open}\text{-}\mathrm{MITL}^{\mathrm{ns}}[\mathsf F_\infty]$ and $\mathsf{Closed}\text{-}\mathrm{MITL}^{\mathrm{ns}}[\mathsf F_\infty]$, which allow only unary non-strict modalities with lower-bound constraints that are all strict, respectively all non-strict (Theorem 2), and that the same four problems are undecidable for safety MTL and coFlat-MTL specifications, in all combinations of $s$ and $b$ (Theorem 3).

Previously, reactive synthesis for timed specifications was known to be undecidable only over infinite words. When the number of clocks, the precision and the number of locations of the controller are all bounded, the problem ($\mathrm{BResRS}$) is decidable, and the source gives an on-the-fly algorithm for it.

## Depends on

- [Metric temporal logic](metric-temporal-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the halting problem for deterministic channel machines, finite automata operating on an unbounded FIFO channel, which is undecidable (Brand and Zafiropulo). From a channel machine $\mathcal S$ one builds MITL formulas $\Omega$ and $\Omega'$ over a trivial plant that force the controller and the environment to propose actions in turn according to the semantics of $\mathcal S$, so that each prefix of its unique computation is encoded as a play, with the channel contents encoded by the timing of the write and read events. $\Omega$ is finite-word realizable exactly when $\mathcal S$ has a halting computation or an infinite computation that never halts, while $\Omega'$ excludes the halting case, so $\mathcal S$ halts if and only if $\Omega$ is realizable and $\Omega'$ is not. The constructed strategies use one clock and bounded precision, which gives the restricted variants, and modifications of the formulas give the fragments and the infinite-word case. A good expansion links a page for the undecidability of halting for deterministic channel machines; none exists yet.

## Sources

- T. Brihaye, M. Estiévenart, G. Geeraerts, H.-M. Ho, B. Monmege and N. Sznajder, "Real-time synthesis is hard!", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2016)*, Lecture Notes in Computer Science 9884, pp. 105–120, Springer, 2016, doi:[10.1007/978-3-319-44878-7_7](https://doi.org/10.1007/978-3-319-44878-7_7); read in arXiv:1606.07124v1 ([arXiv](https://arxiv.org/abs/1606.07124v1)): the definitions of the synthesis problems in Section 2 (Reactive synthesis of timed properties), Proposition 1 (channel machines) and Theorems 1, 2 and 3 in Section 3 (BPrecRS and BClockRS are undecidable) with their proofs in the appendices, and Section 4 (bounded-resources synthesis).
