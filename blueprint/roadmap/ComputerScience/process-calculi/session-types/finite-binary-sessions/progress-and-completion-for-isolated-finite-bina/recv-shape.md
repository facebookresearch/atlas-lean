# Receive obligation on the sole channel forces an input guard

Let $n$, $a$ be natural numbers, $\Gamma$ a session context, $p$ a process and $S$ a session type.
Suppose $\Gamma \vdash_n p$, $\Gamma(c) = \mathrm{end}$ for every $c \ne a$, and $\Gamma(a) = {?S}$.
Then there is a process $q$ with $p = \mathrm{c}_a(\cdot).q$ and $\Gamma[a \mapsto S] \vdash_{n+1}
q$.
