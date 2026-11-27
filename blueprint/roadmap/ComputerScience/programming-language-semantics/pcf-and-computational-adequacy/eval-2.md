# Backward reduction preserves evaluation in PCF

Let $t$, $t'$ and $v$ be closed PCF terms
of type $A$. If $t$ reduces to $t'$ in one call-by-name step and $t'$ evaluates to $v$ in the
big-step call-by-name semantics, then $t$ evaluates to $v$.
