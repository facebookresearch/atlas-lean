# Temporal safety HyperLTL formulas

A HyperLTL formula is temporal safety when its quantifier-free body, read as an LTL formula over trace-indexed propositions, defines a safety property: every violating trace has a finite prefix that no extension repairs.

For a finite set $\mathrm{AP}$ and $\Sigma = 2^{\mathrm{AP}}$, a set $P \subseteq \Sigma^\omega$ of traces is a *safety* property if every $t \notin P$ has a finite prefix $u$ such that no trace extending $u$ is in $P$. A closed [HyperLTL](../hyperltl.md) formula $Q_1\pi_1 \dots Q_n\pi_n.\,\phi$ with quantifier-free body $\phi$ is *temporal safety* if $\phi$, read as an [LTL formula](../../linear-temporal-logic/formula.md) over the propositions $\mathrm{AP}_{\pi_1} \cup \dots \cup \mathrm{AP}_{\pi_n}$, describes a safety property.

Fragments are written with the quantifier prefix as a regular expression and the shape of the body: $\forall\exists^*.\,G$ formulas are $\forall\pi_1\exists\pi_2\dots\exists\pi_m.\,(G\phi) \wedge \phi'$ with $\phi$ and $\phi'$ free of temporal operators, and in $\forall\exists^*.\,G(X^*)$ the formula $\phi$ may use $X$. Such formulas are temporal safety.

## Depends on

- [HyperLTL](../hyperltl.md)
- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Whether a formula is temporal safety is decidable, because safety of an LTL formula is decidable (Sistla); hypersafety in the sense of Clarkson and Schneider is not a syntactic condition. Every $\forall^*\exists^*$ hypersafety property is expressible by a temporal safety formula (Proposition 3.6 of the source).

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Definition 2.1 (safety), Definition 3.3 (temporal safety), Section 2.3 (notation for fragments) and Proposition 3.6 of arXiv:2205.15138v1.
