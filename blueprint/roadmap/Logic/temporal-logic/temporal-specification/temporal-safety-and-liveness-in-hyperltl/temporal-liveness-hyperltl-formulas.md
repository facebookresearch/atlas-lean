# Temporal liveness HyperLTL formulas

A HyperLTL formula is temporal liveness when its quantifier-free body, read as an LTL formula over trace-indexed propositions, defines a liveness property: every finite word extends to a trace satisfying it.

For a finite set $\mathrm{AP}$ and $\Sigma = 2^{\mathrm{AP}}$, a set $P \subseteq \Sigma^\omega$ of traces is a *liveness* property if every finite word $u \in \Sigma^*$ extends to some trace in $P$. A closed [HyperLTL](../hyperltl.md) formula $Q_1\pi_1 \dots Q_n\pi_n.\,\phi$ with quantifier-free body $\phi$ is *temporal liveness* if $\phi$, read as an [LTL formula](../../linear-temporal-logic/formula.md) over the propositions $\mathrm{AP}_{\pi_1} \cup \dots \cup \mathrm{AP}_{\pi_n}$, describes a liveness property.

## Depends on

- [HyperLTL](../hyperltl.md)
- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

Temporal liveness and hyperliveness in the sense of Clarkson and Schneider are incomparable, as the source notes.

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Definition 2.1 (liveness) and Definition 4.1 (temporal liveness) of arXiv:2205.15138v1.
