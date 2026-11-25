# Public announcements with common knowledge do not reduce

Add a common-knowledge operator $C_G$ for groups $G$ of agents to the epistemic language with announcements $[F!]G$, interpreted as in [soundness and completeness of public announcement logic](public-announcement-logic.md). Suppose the language has at least two distinct agents $a \ne b$ and at least two distinct atoms $p \ne q$. Then some formula of the language with announcements and common knowledge, for example $[p!]C_{\{a, b\}}q$, is not equivalent, over all [epistemic models](../model.md), to any announcement-free formula of epistemic logic with common knowledge: announcements with common knowledge are strictly more expressive than epistemic logic with common knowledge. Both hypotheses are needed for the witness: with no agents, common knowledge is trivial and announcements reduce by the ordinary reduction laws, and with $q = p$ the formula $[p!]C_{\{a, b\}}p$ is valid.

## Depends on

- [Epistemic models](../model.md)
- [Soundness and completeness of public announcement logic](public-announcement-logic.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- A model-comparison method for epistemic logic with common knowledge, such as bisimulation games bounded by modal depth, that shows two models agree on all announcement-free formulas of bounded size (proof prerequisite)

## Sources

- A. Baltag and B. Renne, "Dynamic epistemic logic", *Stanford Encyclopedia of Philosophy*, the theorem that public announcement logic with common knowledge is more expressive than epistemic logic with common knowledge, <https://plato.stanford.edu/entries/dynamic-epistemic/>
- A. Baltag, L. S. Moss and S. Solecki, "The logic of public announcements, common knowledge, and private suspicions", *TARK 1998*, 43–56
