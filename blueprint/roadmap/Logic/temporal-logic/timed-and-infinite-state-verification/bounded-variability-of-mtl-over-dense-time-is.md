# Bounded variability of MTL over dense time is undecidable

Over dense time, deciding whether all models of an MTL formula have variability bounded by given v/V is hard for the co-r.e. sets, and deciding whether some such bound exists is Σ⁰₂-hard, so both problems are undecidable.

**Theorem (Furia and Spoletini).** Interpret [MTL](metric-temporal-logic.md) over timed words on $\mathbb R_{\ge 0}$ with the continuous semantics. Let $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ be the problem: given an MTL formula $\varphi$, a natural number $v$ and a natural number $V \ge 1$ in binary, does every model of $\varphi$ have variability bounded by $v/V$? (The source lets $V$ range over $\mathbb T$; its proofs use $V = 1$. For $V = 0$ and $v \ge 1$ every timed word has variability bounded by $v/0$, since timestamps strictly increase, so that case is trivial.) Let $\mathrm{BV}_{\mathbb R_{\ge 0}}$ be the problem: given $\varphi$, are there $v \in \mathbb N$ and $V \ge 1$ such that every model of $\varphi$ has variability bounded by $v/V$? Then $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ is $\Pi^0_1$-hard (co-r.e.-hard, Lemma 8 of the source) and $\mathrm{BV}_{\mathbb R_{\ge 0}}$ is $\Sigma^0_2$-hard (Lemma 10); in particular both are undecidable.

The source also states membership, $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ in $\Pi^0_1$ and $\mathrm{BV}_{\mathbb R_{\ge 0}}$ in $\Sigma^0_2$ (Theorem 6 with Lemmas 7 and 9), but these upper bounds are not established: satisfiability of dense-time MTL, which is $\Sigma^1_1$-hard, reduces to the complement of $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ for every $v$ and every $V \ge 1$. Indeed, conjoining a formula $\psi$ with a formula over $v + 1$ fresh propositions that forces $v + 1$ events strictly inside $(0, 1)$ yields a formula that has a model exactly when $\psi$ does, and none of whose models has variability bounded by $v/V$; in the continuous semantics, adding or removing such events at fresh instants changes no truth value of $\psi$.

Over discrete time $\mathbb N$ with the pointwise semantics both are decidable: $\mathrm{BV}_{\mathbb N}(v, V)$ is EXPSPACE-complete, like satisfiability, and $\mathrm{BV}_{\mathbb N}$ is trivial, since every timed word over $\mathbb N$, with strictly increasing timestamps, has variability bounded by $(x+1)/x$ for every integer $x > 0$: $t_{k+x+1} - t_k \ge x + 1 > x$ (Section 5.2 of the source, which writes $x/x$; that bound fails for the timestamps $t_k = k$, since a closed window of length $x$ then contains $x + 1$ positions). The source notes that the dense-time results transfer to the pointwise semantics when past operators are available.

## Depends on

- [Metric temporal logic](metric-temporal-logic.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces problems about $n$-counter machines with nondeterministic branching. The *bounded counter problem* asks, given $\beta$, whether counter $v_0$ exceeds $\beta$ in some computation ($\Sigma^0_1$-complete), and the *finite counter problem* asks whether some $\beta$ bounds $v_0$ in all computations ($\Sigma^0_2$-complete); both are shown hard by reduction from halting and from the existence of a non-halting computation (Theorem 4). MTL formulas over dense time encode computations so that the value of $v_0$ corresponds to the number of events in a time unit, which reduces these problems to the complements of $\mathrm{BV}(v, V)$ and to $\mathrm{BV}$ (Lemmas 8 and 10). A good expansion adds a page for the $\Sigma^0_2$-completeness of the existence of a non-halting computation of a nondeterministic counter machine, which gives the finite counter problem (Theorem 4 of the source).

## Sources

- C. A. Furia and P. Spoletini, "Bounded Variability of Metric Temporal Logic", in *2014 21st International Symposium on Temporal Representation and Reasoning (TIME 2014)*, IEEE, 2014, pp. 155–163, <https://doi.org/10.1109/TIME.2014.18>; numbers from arXiv:1306.2141v2, <https://arxiv.org/abs/1306.2141v2>: Section 4 (counter problems, Theorem 4), Section 5.1 (Theorem 6, Lemmas 8 and 10, and the membership claims of Lemmas 7 and 9) and Section 5.2.
