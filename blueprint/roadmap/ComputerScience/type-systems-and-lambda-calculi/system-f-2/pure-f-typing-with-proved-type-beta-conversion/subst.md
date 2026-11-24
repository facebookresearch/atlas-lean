# Term substitution preserves Fω typing

Let $\Gamma \vdash t : A$ in pure Fω ([typing](typing.md)) with $\Gamma$ a term context with $m$
variables, let $\Xi$ be a term context with $k$ variables over the same kinding context, and let
$\sigma$ assign to each $i < m$ a term $\sigma(i) \in \mathrm{Tm}_{\Delta,k}$ with $\Xi \vdash
\sigma(i) : \Gamma(i)$. Then $\Xi \vdash t[\sigma] : A$ ([term
substitution](../scoped-pure-f-terms/subst.md)).
