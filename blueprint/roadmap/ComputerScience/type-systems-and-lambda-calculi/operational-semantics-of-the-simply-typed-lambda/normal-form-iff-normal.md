# Call-by-value normal forms are the generic normal forms of the step relation

Consider call-by-value reduction $t \to u$ on intrinsically typed terms of the simply typed lambda calculus (left-to-right and weak: an application first reduces its function position, then its argument once the function is a value, and $(\lambda b)\,a$ contracts to the instantiation $b[a]$ only when $a$ is a value, a value being a lambda abstraction; no step goes under a binder). For every term $t$ of type $A$ in any context $\Gamma$, $t$ is in normal form (for every term $t'$, not $t \to t'$) if and only if $t$ is normal for the one-step relation in the generic sense of a binary relation (there is no $y$ with $t \to y$).

Every lambda abstraction is a normal form here, even one whose body contains a beta-redex.
