# Temporal safety and temporal liveness HyperLTL formulas

A HyperLTL formula is temporal safety (temporal liveness) when its quantifier-free LTL body, read as an LTL formula over trace-indexed propositions, defines a safety (liveness) property. A specification pairs such a formula with an LTL formula that every trace must satisfy.

**Safety and liveness.** For a finite set $\mathrm{AP}$ and $\Sigma = 2^{\mathrm{AP}}$, a set $P \subseteq \Sigma^\omega$ of traces is a *safety* property if every $t \notin P$ has a finite prefix $u$ such that no trace extending $u$ is in $P$; it is a *liveness* property if every finite word $u \in \Sigma^*$ extends to some trace in $P$.

**Temporal safety and liveness.** A closed [HyperLTL](../hyperltl.md) formula $Q_1\pi_1 \dots Q_n\pi_n.\,\phi$ with quantifier-free body $\phi$ is *temporal safety* (resp. *temporal liveness*) if $\phi$, read as an LTL formula over the propositions $\mathrm{AP}_{\pi_1} \cup \dots \cup \mathrm{AP}_{\pi_n}$, describes a safety (resp. liveness) property.

**Specifications.** A *specification* is a pair $(\psi, \varphi)$ of an LTL formula $\psi$ and a HyperLTL formula $\varphi$. It is *satisfiable* if there is a nonempty set $T \subseteq \Sigma^\omega$ with $t \models \psi$ for all $t \in T$ and $T \models \varphi$; satisfiability of $\varphi$ alone is satisfiability of $(\top, \varphi)$. Fragments are written with the quantifier prefix as a regular expression and the shape of the body: for instance $\forall\exists^*.\,G$ formulas are $\forall\pi_1\exists\pi_2\dots\exists\pi_m.\,(G\phi) \wedge \phi'$ with $\phi$ and $\phi'$ free of temporal operators, and in $\forall\exists^*.\,G(X^*)$ the formula $\phi$ may use $X$.

## Depends on

- [HyperLTL](../hyperltl.md)
- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Whether a formula is temporal safety is decidable, because safety of an LTL formula is decidable (Sistla); hypersafety in the sense of Clarkson and Schneider is not a syntactic condition. Every $\forall^*\exists^*$ hypersafety property is expressible by a temporal safety formula (Proposition 3.6 of the source), while temporal liveness and hyperliveness are incomparable.

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Definition 2.1 (safety and liveness), Definition 2.4 (specifications and their satisfiability), Definition 3.3 (temporal safety), Definition 4.1 (temporal liveness), Section 2.3 (notation for fragments) and Proposition 3.6.
