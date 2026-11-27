# Semantic environments for PCF

The ω-complete partial order of environments for a context
$\Gamma$ (a list of PCF types) is defined by recursion on $\Gamma$: the empty context has the
one-point order, and the environments for $\Gamma$ extended by a newest variable of type $A$ are
the pairs $(\eta, a)$ of an environment $\eta$ for $\Gamma$ and an element $a$ of the domain of
$A$, ordered componentwise.
