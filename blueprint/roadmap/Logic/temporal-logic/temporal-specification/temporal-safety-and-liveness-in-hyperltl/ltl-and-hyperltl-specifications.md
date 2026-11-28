# LTL and HyperLTL specifications

A specification pairs an LTL formula, which every trace of a model must satisfy, with a HyperLTL formula, which the set of traces must satisfy; it is satisfiable when some nonempty set of traces meets both.

For a finite set $\mathrm{AP}$ and $\Sigma = 2^{\mathrm{AP}}$, a *specification* is a pair $(\psi, \varphi)$ of an [LTL formula](../../linear-temporal-logic/formula.md) $\psi$ and a closed [HyperLTL](../hyperltl.md) formula $\varphi$. It is *satisfiable* if there is a nonempty set $T \subseteq \Sigma^\omega$ with $t \models \psi$ for all $t \in T$ and $T \models \varphi$; satisfiability of $\varphi$ alone is satisfiability of $(\top, \varphi)$.

## Depends on

- [HyperLTL](../hyperltl.md)
- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

The LTL part describes functional requirements on single traces and the HyperLTL part relational requirements across traces; when $\psi$ is a safety property it can be merged into the HyperLTL formula.

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Definition 2.4 of arXiv:2205.15138v1.
