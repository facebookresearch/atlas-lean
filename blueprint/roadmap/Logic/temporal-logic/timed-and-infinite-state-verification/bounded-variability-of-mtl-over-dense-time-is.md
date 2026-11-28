# Bounded variability of MTL over dense time for a given bound is undecidable

Over dense time, deciding whether all models of an MTL formula have variability bounded by a given v/V is hard for the co-r.e. sets, and so undecidable.

**Theorem (Furia and Spoletini).** Interpret [MTL](metric-temporal-logic.md) over timed words on $\mathbb R_{\ge 0}$ with the continuous semantics. Let $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ be the problem: given an MTL formula $\varphi$, a natural number $v$ and a natural number $V \ge 1$ in binary, does every model of $\varphi$ have variability bounded by $v/V$? (The source lets $V$ range over $\mathbb T$; its hardness proof, Lemma 8, uses $V = 1$. For $V = 0$ and $v \ge 1$ every timed word has variability bounded by $v/0$, since timestamps strictly increase, so that case is trivial.) Then $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ is $\Pi^0_1$-hard (co-r.e.-hard, Lemma 8 of the source); in particular it is undecidable.

The source also considers $\mathrm{BV}_{\mathbb R_{\ge 0}}$, the problem: given $\varphi$, are there $v \in \mathbb N$ and $V \ge 1$ such that every model of $\varphi$ has variability bounded by $v/V$? It states that this problem is $\Sigma^0_2$-hard (Theorem 6 with Lemma 10), but its argument rests on a hardness proof for the finite counter problem that does not go through (see the Expansion), so the theorem above does not include it.

The source also states membership, $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ in $\Pi^0_1$ and $\mathrm{BV}_{\mathbb R_{\ge 0}}$ in $\Sigma^0_2$ (Theorem 6 with Lemmas 7 and 9), but these upper bounds are not established: satisfiability of dense-time MTL, which is $\Sigma^1_1$-hard, reduces to the complement of $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ for every $v$ and every $V \ge 1$, so $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ is not in $\Pi^0_1$. Indeed, for fresh propositions $r_0, \dots, r_v$ let

$$
\theta = \bigwedge_{i \le v} \bigl(\neg r_i \wedge \lozenge_{(0,1)} r_i \wedge \square_{[1,\infty)} \neg r_i\bigr) \wedge \bigwedge_{i \ne j} \square_{[0,\infty)} \neg (r_i \wedge r_j) .
$$

Every model of $\theta$ has $v + 1$ positions, at distinct instants, strictly inside $(0, 1)$, so none has variability bounded by $v/V$. A formula $\psi$ without the $r_i$ is satisfiable exactly when $\psi \wedge \theta$ is: from a model of $\psi$, add positions labeled $\{r_i\}$ at distinct fresh instants of $(0, 1)$; conversely, from a model of $\psi \wedge \theta$, delete the $r_i$ from every label and drop the positions left with an empty label. The $r_i$ hold neither at time $0$ nor from time $1$ on, so this keeps the position at time $0$ and every position from time $1$ on, and the result is a timed word over the original propositions. In the continuous semantics neither step changes the truth value of any atomic proposition of $\psi$ at any instant, so $\psi$ keeps its truth value. The source's proof that $\mathrm{BV}_{\mathbb R_{\ge 0}}$ is in $\Sigma^0_2$ (Lemma 9) enumerates candidate bounds with Lemma 7 as a $\Pi^0_1$ oracle, so that upper bound is unproved as well; this does not show that $\mathrm{BV}_{\mathbb R_{\ge 0}}$ lies outside $\Sigma^0_2$.

Over discrete time $\mathbb N$ with the pointwise semantics both are decidable: $\mathrm{BV}_{\mathbb N}(v, V)$ is EXPSPACE-complete, like satisfiability, and $\mathrm{BV}_{\mathbb N}$ is trivial, since every timed word over $\mathbb N$, with strictly increasing timestamps, has variability bounded by $(x+1)/x$ for every integer $x > 0$: $t_{k+x+1} - t_k \ge x + 1 > x$ (Section 5.2 of the source, which writes $x/x$; that bound fails for the timestamps $t_k = k$, since a closed window of length $x$ then contains $x + 1$ positions). The source notes that the dense-time results transfer to the pointwise semantics when past operators are available.

## Depends on

- [Metric temporal logic](metric-temporal-logic.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces a problem about $n$-counter machines with nondeterministic branching. The *bounded counter problem* asks, given $\beta$, whether counter $v_0$ exceeds $\beta$ in some computation; it is $\Sigma^0_1$-complete, by reduction from halting (Theorem 4). MTL formulas over dense time encode computations so that the value of $v_0$ corresponds to the number of events in a time unit, which reduces the bounded counter problem to the complement of $\mathrm{BV}(v, V)$ with $V = 1$ (Lemma 8).

The source's $\Sigma^0_2$-hardness of $\mathrm{BV}$ is an open repair. Lemma 10 reduces the *finite counter problem*, whether some $\beta$ bounds $v_0$ in all computations, to $\mathrm{BV}$, and Theorem 4 claims that the finite counter problem is $\Sigma^0_2$-complete by reduction from the existence of a non-halting computation. That reduction does not give $\Sigma^0_2$-hardness: a machine starts from a single configuration and each configuration has at most two successors, so by König's lemma some computation does not halt exactly when non-halting computation prefixes of every length exist, a $\Pi^0_1$ condition (and computations that block on decrementing a zero counter add only a $\Sigma^0_1$ alternative). A sound proof that $\mathrm{BV}_{\mathbb R_{\ge 0}}$ is $\Sigma^0_2$-hard needs the $\Sigma^0_2$-hardness of the finite counter problem, for instance by reduction from finiteness of a recursively enumerable set, which Lemma 10 would then transfer; until a source establishes that step, the $\Sigma^0_2$-hardness of $\mathrm{BV}_{\mathbb R_{\ge 0}}$ remains an open repair rather than a result.

A good expansion adds a page for the $\Sigma^0_1$-completeness of the bounded counter problem (Theorem 4 of the source).

## Sources

- C. A. Furia and P. Spoletini, "Bounded Variability of Metric Temporal Logic", in *2014 21st International Symposium on Temporal Representation and Reasoning (TIME 2014)*, IEEE, 2014, pp. 155–163, <https://doi.org/10.1109/TIME.2014.18>; numbers from arXiv:1306.2141v2, <https://arxiv.org/abs/1306.2141v2>: Section 4 (counter problems, Theorem 4), Section 5.1 (Theorem 6, Lemma 8, and the claims of Lemmas 7, 9 and 10) and Section 5.2.
