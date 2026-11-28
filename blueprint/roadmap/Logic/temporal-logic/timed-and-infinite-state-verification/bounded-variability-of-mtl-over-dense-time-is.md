# Bounded variability of MTL over dense time is undecidable

Over dense time, deciding whether all models of an MTL formula have variability bounded by given v/V is complete for the co-r.e. sets, and deciding whether some such bound exists is Σ⁰₂-complete.

**Theorem (Furia and Spoletini).** Interpret [MTL](metric-temporal-logic.md) over timed words on $\mathbb R_{\ge 0}$ with the continuous semantics. Let $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ be the problem: given an MTL formula $\varphi$ and natural numbers $v$ and $V$ in binary, does every model of $\varphi$ have variability bounded by $v/V$? (The source lets $V$ range over $\mathbb T$; its semi-decision procedure, Lemma 7, uses $V + 1$ as an endpoint of an MTL interval, which needs an integer.) Let $\mathrm{BV}_{\mathbb R_{\ge 0}}$ be the problem: given $\varphi$, are there $v, V$ such that every model of $\varphi$ has variability bounded by $v/V$? Then $\mathrm{BV}_{\mathbb R_{\ge 0}}(v, V)$ is $\Pi^0_1$-complete (co-r.e.-complete) and $\mathrm{BV}_{\mathbb R_{\ge 0}}$ is $\Sigma^0_2$-complete (Theorem 6 of the source).

Both problems are thus undecidable, but of lower degree than dense-time MTL satisfiability, which is $\Sigma^1_1$-hard. Over discrete time $\mathbb N$ with the pointwise semantics both are decidable: $\mathrm{BV}_{\mathbb N}(v, V)$ is EXPSPACE-complete, like satisfiability, and $\mathrm{BV}_{\mathbb N}$ is trivial, since every discrete-time formula has variability bounded by $x/x$ for every integer $x > 0$ (Section 5.2 of the source). The source notes that the dense-time results transfer to the pointwise semantics when past operators are available.

## Depends on

- [Metric temporal logic](metric-temporal-logic.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

*Upper bounds.* $\mathrm{BV}(v, V)$ is semi-decided by searching for a model that violates the bound: restricting $\varphi$ to a finite time horizon makes all its models of bounded variability, and satisfiability over models of a given bounded variability is decidable, so the complement of $\mathrm{BV}(v, V)$ is r.e. and $\mathrm{BV}(v, V)$ is in $\Pi^0_1$ (Lemma 7). $\mathrm{BV}$ is in $\Sigma^0_2$ by dovetailing over pairs $(v, \varphi)$ with an oracle for $\mathrm{BV}(v, V)$ (Lemma 9).

*Lower bounds.* The proof reduces problems about $n$-counter machines with nondeterministic branching. The *bounded counter problem* asks, given $\beta$, whether counter $v_0$ exceeds $\beta$ in some computation ($\Sigma^0_1$-complete), and the *finite counter problem* asks whether some $\beta$ bounds $v_0$ in all computations ($\Sigma^0_2$-complete); both are shown hard by reduction from halting and from the existence of a non-halting computation (Theorem 4). MTL formulas over dense time encode computations so that the value of $v_0$ corresponds to the number of events in a time unit, which reduces these problems to the complements of $\mathrm{BV}(v, V)$ and to $\mathrm{BV}$ (Lemmas 8 and 10).

## Sources

- C. A. Furia and P. Spoletini, "Bounded Variability of Metric Temporal Logic", in *2014 21st International Symposium on Temporal Representation and Reasoning (TIME 2014)*, IEEE, 2014, pp. 155–163, <https://doi.org/10.1109/TIME.2014.18>; numbers from arXiv:1306.2141v2, <https://arxiv.org/abs/1306.2141v2>: Section 4 (counter problems, Theorem 4), Section 5.1 (Theorem 6 with Lemmas 7 to 10) and Section 5.2.
