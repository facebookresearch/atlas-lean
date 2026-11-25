# Soundness of the PCF denotational semantics

Let $A$ be a PCF type and let $t$ and $v$
be closed terms of type $A$. If $t$ evaluates to $v$ under big-step call-by-name evaluation,
then for every environment $\eta$ of the empty context, the denotations of $t$ and $v$ at
$\eta$ are equal.
