# Send obligation on the sole channel forces an output guard

Let $n$, $a$ be natural numbers, $\Gamma$ a session context, $p$ a process and $S$ a session type.
Suppose $\Gamma \vdash_n p$, $\Gamma(c) = \mathrm{end}$ for every $c \ne a$, and $\Gamma(a) = {!S}$.
Then there are a name $b$ and a process $q$ with $p = \overline{\mathrm{c}_a}\langle b\rangle.q$,
$b$ in scope at depth $n$, and $\Gamma[a \mapsto S] \vdash_n q$.
