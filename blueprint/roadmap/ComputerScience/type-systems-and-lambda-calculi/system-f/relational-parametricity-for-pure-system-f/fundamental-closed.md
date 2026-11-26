# Closed typed System F terms are related to themselves

Let $\Gamma$ be a term context with no term variables over $n$ type variables, $t \in \mathrm{Tm}_{n,0}$ and $A \in \mathrm{Ty}_n$ with $\Gamma \vdash t : A$ ([typing](../the-five-typing-rules-of-pure-system-f/typing.md)). For every assignment $\rho$ of [β-invariant relations](../binary-beta-invariant-relations/rel.md) to the type variables, the [erasure](../system-f-erasure-and-closing-environments/erase-model.md) of $t$ is related to itself by $[\![A]\!]_\rho$ ([relational interpretation](../impredicative-binary-interpretation-of-system-f/interpret.md)).

## Informally uses

- [Fundamental theorem of relational parametricity for System F](fundamental.md): the case of no term variables.
