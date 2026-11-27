# Evaluation of an application depends on the function only through its results

Let $F$
and $F'$ be terms of type $C \to D$ in a context $\Xi$ such that, for every term $u$, $F$ evaluates
to $u$ under call-by-value big-step evaluation if and only if $F'$ does. Then for every term $a$ of
type $C$ and every term $w$ of type $D$ in $\Xi$, the application $F\, a$ evaluates to $w$ if and
only if $F'\, a$ evaluates to $w$.
