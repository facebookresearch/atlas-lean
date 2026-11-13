# Substitution lemma for STLC denotation

For every interpretation $I$ of the base types,
every type-preserving substitution $\sigma$ mapping each variable of a context $\Gamma$ to a term
in a context $\Delta$, every term $t$ in context $\Gamma$ and every environment $\eta$ for
$\Delta$, the denotation in $\eta$ of $t$ with $\sigma$ applied simultaneously to its variables
equals the denotation of $t$ in the environment that sends each variable $x$ of $\Gamma$ to the
denotation of $\sigma(x)$ in $\eta$.
