# Term-binder instantiation preserves Fω typing

Let $\Gamma$ be a term context, $A, B \in \mathrm{Ty}^{\star}_{\Delta}$, $b \in
\mathrm{Tm}_{\Delta,m+1}$ and $a \in \mathrm{Tm}_{\Delta,m}$ with $A \cdot \Gamma \vdash b : B$ and
$\Gamma \vdash a : A$ ([typing](typing.md)). Then $\Gamma \vdash b[a] : B$
([instantiation](../scoped-pure-f-terms/instantiate.md)).
