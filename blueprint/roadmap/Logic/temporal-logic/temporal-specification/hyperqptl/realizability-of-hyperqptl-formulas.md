# Realizability of HyperQPTL formulas

A HyperQPTL formula over inputs $I$ and outputs $O$ is realizable if some strategy, mapping each finite sequence of input valuations to an output valuation, produces a set of traces that satisfies the formula.

Let $\mathrm{AP} = I \cup O$ with $I \cap O = \varnothing$. A *strategy* is a function $f : (2^I)^* \to 2^O$. For an input word $w = w_0 w_1 w_2 \cdots \in (2^I)^\omega$ the strategy produces the trace

$$
(f(\varepsilon) \cup w_0)\,(f(w_0) \cup w_1)\,(f(w_0 w_1) \cup w_2) \cdots \in (2^{I \cup O})^\omega,
$$

and the set of traces of $f$ consists of these traces for all input words. A [HyperQPTL](hyperqptl.md) formula $\varphi$ over $\mathrm{AP}$ is *realizable* if there is a strategy whose set of traces satisfies $\varphi$; quantified propositions are treated as outputs. The *realizability problem* asks, given $I$, $O$ and $\varphi$, whether $\varphi$ is realizable. Realizability for QPTL and HyperLTL formulas is the special case of formulas in those fragments.

## Depends on

- [HyperQPTL](hyperqptl.md)

## Proof depends on

None.

## Expansion

The traces of a strategy form a strategy tree branching on input valuations, so realizability asks for a set of traces of a special, input-complete shape, in contrast with satisfiability, which allows any set. The source recalls that distributed realizability of QPTL is undecidable in general, as for LTL, and decidable for architectures without information forks (Section 4).

## Sources

- B. Finkbeiner, C. Hahn, J. Hofmann and L. Tentrup, "Realizing ω-regular hyperproperties", in *Computer Aided Verification (CAV 2020)*, Lecture Notes in Computer Science 12225, Springer, 2020, pp. 40–63, doi:10.1007/978-3-030-53291-8_4; read as arXiv:2101.07161v1, <https://arxiv.org/abs/2101.07161v1>: Section 4 (strategies and Definition 1, HyperQPTL realizability).
