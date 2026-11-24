# Strong normalization for call-by-value reduction

Consider call-by-value reduction $t \to u$ on intrinsically typed terms of the simply typed lambda calculus (left-to-right and weak: an application first reduces its function position, then its argument once the function is a value, and $(\lambda b)\,a$ contracts to the instantiation $b[a]$ only when $a$ is a value, a value being a lambda abstraction; no step goes under a binder). A term $t$ of type $A$ in context $\Gamma$ is strongly normalizing when it is accessible for the converse of one-step reduction (the relation in which $t'$ precedes $t$ exactly when $t \to t'$): inductively, $t$ is strongly normalizing when every $t'$ with $t \to t'$ is strongly normalizing.

Because reduction never goes under a binder, this is termination of the weak call-by-value strategy, not strong normalization of full beta reduction.
