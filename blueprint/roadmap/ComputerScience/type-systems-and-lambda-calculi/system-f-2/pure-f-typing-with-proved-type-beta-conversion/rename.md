# Term renaming preserves Fω typing

Let $\Gamma \vdash t : A$ in pure Fω ([typing](typing.md)) with $\Gamma$ a term context with $m$
variables, let $\Xi$ be a term context with $k$ variables over the same kinding context, and let
$\rho : \{0, \dots, m-1\} \to \{0, \dots, k-1\}$ satisfy $\Xi(\rho(i)) = \Gamma(i)$ for every $i <
m$. Then $\Xi \vdash t\langle\rho\rangle : A$ ([term renaming](../scoped-pure-f-terms/rename.md)).
