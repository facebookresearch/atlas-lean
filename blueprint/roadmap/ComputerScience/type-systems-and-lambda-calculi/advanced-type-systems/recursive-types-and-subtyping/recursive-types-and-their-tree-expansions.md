# Recursive types and their tree expansions

*Recursive types* are given by $\alpha ::= t \mid \bot \mid \top \mid \alpha \to \beta \mid \mu t.\, \alpha$, where $t$ ranges over type variables and constants and $\mu t$ binds $t$;
types are identified up to renaming of bound variables. Unlike the iso-recursive reading, in which $\mathrm{fold}$ and $\mathrm{unfold}$ coerce between
$\mu t.\, \alpha$ and its unfolding $[\mu t.\, \alpha / t]\alpha$, the equi-recursive reading treats a recursive type and its unfolding as interchangeable.

- **Trees.** A tree over the ranked labels $\{\bot^0, \top^0, \to^2\} \cup \{t^0\}$ is a partial map $A$ from finite sequences of natural numbers (paths) to labels whose
  domain is non-empty and prefix-closed, in which a node labeled with a symbol of rank $i$ has exactly the children $0, \dots, i-1$.
- **Tree expansion.** The tree $T\alpha$ of a type is defined by $T(\alpha \to \beta)(\mathrm{nil}) = {\to}$, $T(\alpha \to \beta)(0\pi) = T\alpha(\pi)$,
  $T(\alpha \to \beta)(1\pi) = T\beta(\pi)$, $T(t)(\mathrm{nil}) = t$, $T(\bot)(\mathrm{nil}) = \bot$, $T(\top)(\mathrm{nil}) = \top$, $T(\mu t.\, \alpha) = \bot$ when $\alpha$ has the form
  $\mu t_1 \dots \mu t_n.\, t$ with each $t_i \ne t$, and $T(\mu t.\, \alpha) = T([\mu t.\, \alpha / t]\alpha)$ otherwise (by induction on the path length and the number of
  leading $\mu$'s).
- **Properties.** Every $T\alpha$ is a *regular* tree, with finitely many distinct subtrees; deciding $T\alpha = T\beta$ therefore reduces to equivalence of
  deterministic finite automata. $T$ is a bijection between μ-free types and finite trees. For example $T(\mu t.\, s \to s \to t) = T(\mu t.\, s \to t)$,
  although the two types are not related by finitely many foldings and unfoldings.
- **Metric.** The distance between trees $A$ and $B$ is $d(A, B) = 0$ if $A = B$, and otherwise $d(A, B) = 2^{-k}$, where $k$ is the length of a shortest path at which $A$ and
  $B$ differ (one is defined there and the other is not, or both are defined with different labels). The trees form a complete metric space for $d$, the
  completion of the space of finite trees.
- **Contractiveness.** $\alpha$ is *contractive* in $t$ if $t$ is not free in $\alpha$ or $\alpha$ unfolds to a type of the form $\alpha_1 \to \alpha_2$; then $A \mapsto [A/t]T\alpha$ is
  a contraction for $d$ (it at least halves distances). By Banach's fixed-point theorem such a map has a unique fixed point.

## Background

- [Iso-recursive types: safety without normalization](../iso-recursive-types-safety-without-normalization.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 2.1 (types), Section 3.2 (folding and unfolding), Section 3.3 (trees, the definition of $T$, Remarks 3.3.1–3.3.4, and the metric and Banach's theorem in Remark 3.3.2) and the opening of Section 5.1 (contractiveness).
