# Existence of analytic solutions of algebraic differential equations is undecidable

No algorithm decides whether an algebraic differential equation with integer coefficients has a real analytic solution on [0, ∞), even when the input is restricted to equations with a unique analytic solution near 0.

**Theorem (Denef and Lipshitz).** The following problem is undecidable: given $P \in \mathbb Z[x, y_1, y_2, \ldots, y_n]$, does the algebraic differential equation

$$
P(x, y', y'', \ldots, y^{(n)}) = 0
$$

admit a real analytic solution $y$ on $[0, \infty)$? It remains undecidable when the input is restricted to equations that have a unique analytic solution in a neighborhood of $0$.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable](../../../real-functions/undecidable-problems-for-elementary-functions/sign-and-zeros-of-one-variable-sine-terms.md)

## Expansion

The idea of the proof is to take a function built from the sine function, as in Richardson's theorem, for which one cannot decide whether it is everywhere positive, and to show that its reciprocal satisfies an algebraic differential equation; the details of the encoding are in the source. The closure of the class of differentially algebraic functions under the operations used is a lemma without a page here. To avoid $\pi$ among the coefficients, Denef and Lipshitz used that $\tan^{-1} x$ satisfies an algebraic differential equation and tends to $\pi/2$ as $x \to +\infty$; Laczkovich's elimination of $\pi$ is an alternative.

## Sources

- J. Denef and L. Lipshitz, "Decision problems for differential equations", *Journal of Symbolic Logic* 54(3), 1989, pp. 941–950, <https://doi.org/10.2307/2274755>: Theorem 4.1 (cited after the survey below).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Section 9.4 ("Differential equations") of that version, with the remark after the problem statement on avoiding $\pi$.
