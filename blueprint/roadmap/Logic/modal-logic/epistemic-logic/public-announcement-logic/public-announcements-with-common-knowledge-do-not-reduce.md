# Public announcements with common knowledge do not reduce

Add a common-knowledge operator $C_G$ for sets $G$ of agents to the epistemic language with announcements $[F!]\psi$ of [soundness and completeness of public announcement logic](public-announcement-logic.md), with the [satisfaction relation](../sat.md) of epistemic formulas: $M, w \models C_G \varphi$ holds when $M, v \models \varphi$ for every world $v$ reachable from $w$ by a path of length zero or more along the union $\bigcup_{i \in G} R_i$ of the agents' accessibility relations, the zero-step operator of [common knowledge as a greatest fixed point](../common-knowledge-as-a-greatest-fixed-point.md). Suppose the language has at least two distinct agents $a \ne b$ and at least two distinct atoms $p \ne q$. Then some formula of the language with announcements and common knowledge, for example $[p!]C_{\{a, b\}}q$, is not equivalent, over the [epistemic models](../model.md) in which every accessibility relation is an equivalence relation, to any announcement-free formula of epistemic logic with common knowledge: announcements with common knowledge are strictly more expressive than epistemic logic with common knowledge. Both hypotheses are needed for the witness: with no agents, $C_\emptyset \varphi$ is equivalent to $\varphi$ and announcements reduce by the ordinary reduction laws, and with $q = p$ the formula $[p!]C_{\{a, b\}}p$ is valid.

## Depends on

- [Epistemic models](../model.md)
- [Satisfaction in an epistemic model](../sat.md)
- [Common knowledge as a greatest fixed point](../common-knowledge-as-a-greatest-fixed-point.md)
- [Soundness and completeness of public announcement logic](public-announcement-logic.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- A model-comparison method for epistemic logic with common knowledge, such as bisimulation games bounded by modal depth, that shows two models agree on all announcement-free formulas of bounded size (proof prerequisite)

## Sources

- A. Baltag and B. Renne, "Dynamic epistemic logic", *Stanford Encyclopedia of Philosophy*, the theorem that public announcement logic with common knowledge is more expressive than epistemic logic with common knowledge, <https://plato.stanford.edu/entries/dynamic-epistemic/>
- A. Baltag, L. S. Moss and S. Solecki, "The logic of public announcements, common knowledge, and private suspicions", *TARK 1998*, 43–56
- H. van Ditmarsch, W. van der Hoek and B. Kooi, *Dynamic Epistemic Logic*, Springer, 2007, Chapter 8 (expressivity of public announcement logic with common knowledge over S5 models)
