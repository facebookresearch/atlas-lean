# Extending a semantic environment in STLC

Given an interpretation $I$ of the base types, a
value $a$ in the denotation of a type $A$ and an environment $\eta$ for a context $\Gamma$, the
extended environment for the context $A :: \Gamma$ sends the newest variable to $a$ and the
successor $\mathrm{succ}\,x$ of each variable $x$ of $\Gamma$ to $\eta(x)$.
