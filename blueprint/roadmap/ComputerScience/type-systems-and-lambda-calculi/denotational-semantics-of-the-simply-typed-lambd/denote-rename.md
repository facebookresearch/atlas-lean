# Renaming lemma for STLC denotation

For every interpretation $I$ of the base types, every
type-preserving renaming $\rho$ from context $\Gamma$ to context $\Delta$, every term $t$ in
context $\Gamma$ and every environment $\eta$ for $\Delta$, the denotation in $\eta$ of the term
obtained by renaming the variables of $t$ along $\rho$ equals the denotation of $t$ in the
environment that sends each variable $x$ of $\Gamma$ to $\eta(\rho(x))$.
