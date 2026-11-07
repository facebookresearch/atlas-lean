# Denotation of an instantiated STLC body

For every interpretation $I$ of the base types,
every term $b$ of type $B$ in context $A :: \Gamma$, every term $a$ of type $A$ in context $\Gamma$
and every environment $\eta$ for $\Gamma$, the denotation in $\eta$ of $b$ with its newest variable
replaced by $a$ equals the denotation of $b$ in the environment that extends $\eta$ by the
denotation of $a$ in $\eta$ for the newest variable.
