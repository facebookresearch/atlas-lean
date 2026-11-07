# Big-step evaluation is closed under backward reduction steps

Let $t$, $t'$ and $v$ be
terms of the same type $A$ in the same typing context $\Gamma$. If $t$ reduces to $t'$ in one
left-to-right call-by-value step and $t'$ evaluates to $v$ in the big-step semantics, written
$t' \Downarrow v$, then $t \Downarrow v$.
