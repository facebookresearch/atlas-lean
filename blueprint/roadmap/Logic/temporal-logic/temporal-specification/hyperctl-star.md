# HyperCTL*

*HyperCTL** formulas allow path quantifiers anywhere: $\varphi ::= a_\pi \mid \neg\varphi \mid \varphi \vee \varphi \mid \mathbf X\varphi \mid \varphi\ \mathbf U\ \varphi \mid \exists\pi.\ \varphi$, with $\forall\pi.\varphi = \neg\exists\pi.\neg\varphi$.
Over a Kripke structure $K = (S, s_0, \delta, AP, L)$, path variables range over paths $p \in (S \times 2^{AP})^\omega$ of $K$, and the clauses are those of [HyperLTL](hyperltl.md) except that
$\Pi \models_K \exists\pi.\varphi$ iff some path $p$ of $K$ starting at the current state of the most recently quantified path (the initial state if $\Pi$ is empty) has
$\Pi[\pi \mapsto p] \models_K \varphi$. A *specification* is a Boolean combination of closed formulas each beginning with a quantifier. The *alternation depth* of a formula in negation
normal form is the largest number of alternations between existential and universal quantifiers along a path of its syntax tree, each $\mathbf U$ or $\mathbf R$ counting as one
more alternation.

## Depends on

- [HyperLTL](hyperltl.md)

## Sources

- M. R. Clarkson, B. Finkbeiner, M. Koleini, K. K. Micinski, M. N. Rabe and C. Sánchez, "Temporal logics for hyperproperties", *Principles of Security and Trust (POST 2014)*, Lecture Notes in Computer Science 8414, Springer, 2014, pp. 265–284, extended version arXiv:1401.4492, <https://arxiv.org/abs/1401.4492>: Section 4 (syntax and semantics of HyperCTL*) and Section 6, Definition 1 (alternation depth).
