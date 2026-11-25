# Communication preserves binary session typing

Let $\Gamma$ be a session context and let $r$, $t$ be pairs of π-calculus processes. If $r \to t$ is
a communication step and $r$ is binary typed in $\Gamma$ (the first thread typed in $\Gamma$ and the
second in the pointwise dual $\overline{\Gamma}$, both with no enclosing binders), then there are a
channel number $a$ and a session type $S$ such that $\Gamma(a) = {!S}$ or $\Gamma(a) = {?S}$, and
$t$ is binary typed in $\Gamma[a \mapsto S]$, the context that maps $a$ to $S$ and agrees with
$\Gamma$ elsewhere.
