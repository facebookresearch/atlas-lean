# Metric temporal logic

Metric temporal logic (MTL) extends LTL by attaching to each until operator an interval of the time domain that bounds the distance to the position where its target holds; it is interpreted over timed words.

**Definition.** Let the time domain $\mathbb T$ be $\mathbb N$ or $\mathbb R_{\ge 0}$, and $P$ a finite set of atomic propositions. A *timed word* is an infinite sequence $\omega = (\sigma_0, t_0)(\sigma_1, t_1)\cdots$ of nonempty sets $\sigma_k \subseteq P$ and timestamps $t_k \in \mathbb T$ that are strictly increasing and divergent, with $t_0 = 0$. MTL formulas are

$$
\varphi ::= \top \mid p \mid \neg\varphi \mid \varphi \wedge \varphi \mid \mathsf U_J(\varphi, \varphi),
$$

with $p \in P$ and $J$ an interval of $\mathbb T$ with integer endpoints (constants in binary). The *pointwise* semantics evaluates formulas at positions: $\omega, k \models_p \mathsf U_J(\varphi_1, \varphi_2)$ iff there is $h > k$ with $t_h - t_k \in J$, $\omega, h \models_p \varphi_2$ and $\omega, x \models_p \varphi_1$ for all $k < x < h$, and $\omega \models_p \varphi$ iff $\omega, 0 \models_p \varphi$. The *continuous* semantics evaluates formulas at time instants $t \in \mathbb T$: $\omega, t \models_c p$ iff $t = t_k$ and $p \in \sigma_k$ for some $k$, and $\omega, t \models_c \mathsf U_J(\varphi_1, \varphi_2)$ iff there is $u > t$ with $u - t \in J$, $\omega, u \models_c \varphi_2$ and $\omega, v \models_c \varphi_1$ for all $t < v < u$. Derived operators are $\lozenge_J\varphi = \mathsf U_J(\top, \varphi)$ and $\square_J\varphi = \neg\lozenge_J\neg\varphi$.

A timed word has *variability bounded by $v/V$* ($v \in \mathbb N$, $V \in \mathbb T$) if no closed time interval of length $V$ contains more than $v$ of its positions: $t_{k+v} - t_k > V$ for all $k$.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Timed words and timed languages](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-words-and-timed-languages.md)

## Proof depends on

None.

## Expansion

Over dense time the continuous semantics is strictly more expressive than the pointwise one. Satisfiability of MTL over dense time is highly undecidable, $\Sigma^1_1$-hard (Alur and Henzinger), whereas over discrete time it is EXPSPACE-complete. Restricting to models with bounded variability makes reasoning simpler, which motivates asking which formulas have only models of bounded variability.

## Sources

- C. A. Furia and P. Spoletini, "Bounded Variability of Metric Temporal Logic", in *2014 21st International Symposium on Temporal Representation and Reasoning (TIME 2014)*, IEEE, 2014, pp. 155–163, <https://doi.org/10.1109/TIME.2014.18>; numbers from arXiv:1306.2141v2, <https://arxiv.org/abs/1306.2141v2>: Section 2 (timed words, variability), Section 3 (syntax, pointwise and continuous semantics, complexity of satisfiability) and Remark 1.
- R. Alur and T. A. Henzinger, "Real-time logics: complexity and expressiveness", *Information and Computation* 104(1):35–77, 1993, <https://doi.org/10.1006/inco.1993.1025>: complexity of MTL satisfiability, as recalled in Section 3 of the version of the first source read.
