# Pointwise semantic equality of substitutions

Fix an interpretation $I$ of the base types
as types. Two simultaneous substitutions $\sigma$ and $\tau$ from a context $\Gamma$ to a context
$\Delta$ are pointwise semantically equal in $I$ when, for every variable $x$ of $\Gamma$ (of any
type) and every semantic environment $\eta$ for $\Delta$, the denotation of the term $\sigma(x)$ in
$I$ at $\eta$ equals the denotation of the term $\tau(x)$ in $I$ at $\eta$.
