# Big-step evaluation is closed under backward multi-step reduction

Let $t$, $t'$ and $v$
be terms of the same type $A$ in the same typing context $\Gamma$. If $t$ reduces to $t'$ in
finitely many (possibly zero) left-to-right call-by-value steps and $t'$ evaluates to $v$ in the
big-step semantics, written $t' \Downarrow v$, then $t \Downarrow v$.
