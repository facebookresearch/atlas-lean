# Whether a Presburger counter machine is well structured is undecidable

Well-structured transition systems have decidable coverability and termination, but deciding whether a given counter machine is well structured for the usual order on counter values is undecidable, already for one-counter machines with Presburger-definable functions and for two-counter Minsky machines or affine VASS.

**Setting (Finkel and Gupta).** A quasi-order is a *well quasi-order* if every infinite sequence $e_0, e_1, \dots$ has indices $i < j$ with $e_i \le e_j$. An ordered transition system $(X, \to, \le)$ is *monotone* if whenever $s \to t$ and $s' \ge s$, there is $t' \ge t$ with $s' \to^\ast t'$, and *strongly monotone* if moreover one step suffices, $s' \to t'$. It is a *well-structured transition system* (WSTS) if $\le$ is a well quasi-order and the system is monotone. A $d$-dimensional *Presburger counter machine* (PCM) $M = (Q, \Phi, \to)$ has a finite set of control states $Q$ and transitions $q \xrightarrow{\varphi} q'$ labeled by quantifier-free Presburger formulas $\varphi(x_1, \dots, x_d, x'_1, \dots, x'_d)$ with congruences, relating counter values before and after the step; it is *functional* if each formula defines a partial function. Minsky machines (increments, decrements, zero tests) and affine VASS ($d$-AVASS, where each transition applies an affine map $\vec x \mapsto A\vec x + \vec b$ with $A \in \mathbb Z^{d \times d}$, $\vec b \in \mathbb Z^d$ on its domain in $\mathbb N^d$) are PCMs. Configurations $Q \times \mathbb N^d$ are ordered by $(q, \vec x) \le (q', \vec y)$ iff $q = q'$ and $\vec x \le \vec y$ componentwise. The *well structured problem* asks whether a given PCM, with this order, is a WSTS.

**Theorem (Finkel and Gupta).** The well structured problem is undecidable for functional one-dimensional PCMs, for two-counter Minsky machines, and for two-dimensional affine VASS.

In contrast, the same paper shows that the well structured problem is decidable for one-dimensional affine VASS, and that the *strong* well structured problem (is the PCM a WSTS with strong monotony?) is decidable for all PCMs, since strong monotony is expressible in Presburger arithmetic.

## Depends on

- [Well-structured transition systems](../../../../../Logic/temporal-logic/timed-and-infinite-state-verification/well-structured-transition-systems.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

All three cases use one general lemma reducing control-state reachability in two-counter Minsky machines: suppose that from a machine $M$ with initial state $q_0$ and target state $q_1$ one can build a machine $N$ of the class such that $N$ is a WSTS whenever every control state of $M$ is reachable, and $N$ is a WSTS only if $q_1$ is reachable from $(q_0; 0, 0)$. Applying the construction to each of the finitely many submachines of $M$ on control-state sets containing $q_0$ and $q_1$ then decides reachability of $q_1$, so the well structured problem for the class is undecidable. The constructions simulate the Minsky machine by a functional one-dimensional PCM, and by a four-counter Minsky machine that is in turn simulated by a two-counter one, extended with a reset circuit leading back to the initial configuration. Two-dimensional affine VASS simulate zero tests by the maps $\mathrm{diag}(-1, 1)$ and $\mathrm{diag}(1, -1)$: the update $x' = -x$ stays in $\mathbb N$ only when $x = 0$.

## Sources

- Alain Finkel and Ekanshdeep Gupta, "The Well Structured Problem for Presburger Counter Machines", in *39th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2019)*, Leibniz International Proceedings in Informatics 150, Schloss Dagstuhl, 2019, pp. 41:1–41:15, doi:[10.4230/LIPIcs.FSTTCS.2019.41](https://doi.org/10.4230/LIPIcs.FSTTCS.2019.41); read in arXiv:1910.02736v2 ([arXiv](https://arxiv.org/abs/1910.02736v2)), whose numbering is used: Section 2 (arithmetic and Presburger counter machines, affine VASS, monotony and WSTS), Lemma 13, Theorem 16 (functional one-dimensional PCMs), Theorem 19 (two-counter Minsky machines), Corollary 20 (two-dimensional affine VASS), the decidability of the strong well structured problem in Section 3, and Theorem 31 (one-dimensional affine VASS).
