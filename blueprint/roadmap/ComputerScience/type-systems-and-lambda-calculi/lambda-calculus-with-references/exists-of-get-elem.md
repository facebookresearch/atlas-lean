# Well-typed stores hold a typed value at every location

Let $\Gamma$ be a typing
context, $S$ a store typing, and $\mu$ a store (a list of terms, whose entry at index $l$ is
the contents of location $l$) that is well typed, $\Gamma \mid S \vdash \mu$. If $S$ assigns
type $T$ to location $l$, then $\mu$ has an entry $v$ at location $l$, $v$ is a value, and
$\Gamma \mid S \vdash v : T$.
