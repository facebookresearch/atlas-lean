# HyperCTL*

*HyperCTL** formulas allow path quantifiers anywhere: $\varphi ::= a_\pi \mid \neg\varphi \mid \varphi \vee \varphi \mid \mathbf X\varphi \mid \varphi\ \mathbf U\ \varphi \mid \exists\pi.\ \varphi$, with $\forall\pi.\varphi = \neg\exists\pi.\neg\varphi$.
Over a Kripke structure $K = (S, s_0, \delta, AP, L)$ in which every state has a successor, a *path* is a sequence $p = (s_0', L(s_0'))(s_1', L(s_1'))\cdots \in (S \times 2^{AP})^\omega$
with $s_{i+1}' \in \delta(s_i')$ for all $i$, and path variables range over paths. An atom is read from the label of the current state: if $\Pi(\pi)[0] = (s, L(s))$, then $\Pi \models_K a_\pi$ iff
$a \in L(s)$. The other clauses are those of [HyperLTL](hyperltl.md), with suffixes of paths, except that
$\Pi \models_K \exists\pi.\varphi$ iff some path $p$ of $K$ starting at the current state of the most recently quantified path (the initial state if $\Pi$ is empty) has
$\Pi[\pi \mapsto p] \models_K \varphi$. A *specification* is a Boolean combination of closed formulas each beginning with a quantifier. The *alternation depth* of a formula in negation
normal form is the largest number of alternations between existential and universal quantifiers along a path of its syntax tree, each $\mathbf U$ or $\mathbf R$ counting as one
more alternation.

## Depends on

- [HyperLTL](hyperltl.md)

## Sources

- M. R. Clarkson, B. Finkbeiner, M. Koleini, K. K. Micinski, M. N. Rabe and C. Sánchez, "Temporal logics for hyperproperties", *Principles of Security and Trust (POST 2014)*, Lecture Notes in Computer Science 8414, Springer, 2014, pp. 265–284, extended version arXiv:1401.4492, <https://arxiv.org/abs/1401.4492>: Section 2 (Kripke structures, in which every state has a successor, and their paths) and Section 4 (syntax and semantics of HyperCTL*, with atoms read from the label of the current state) and Section 6, Definition 1 (alternation depth).
