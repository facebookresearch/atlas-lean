# Weakening preserves STLC denotation

For every interpretation $I$ of the base types, every
term $t$ of type $A$ in context $\Gamma$, every type $B$, every value $a$ in the denotation of $B$
and every environment $\eta$ for $\Gamma$, the weakening of $t$ to the context $B :: \Gamma$ has,
in the environment that extends $\eta$ by $a$ for the newest variable, the same denotation as $t$
in $\eta$.
