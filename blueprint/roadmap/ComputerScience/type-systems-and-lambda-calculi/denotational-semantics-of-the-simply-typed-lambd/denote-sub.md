# Denotation of an STLC substitution

Given an interpretation $I$ of the base types, a
type-preserving substitution $\sigma$ mapping each variable of a context $\Gamma$ to a term in a
context $\Delta$, and an environment $\eta$ for $\Delta$, this is the environment for $\Gamma$
that sends each variable $x$ to the denotation of $\sigma(x)$ in $\eta$.
