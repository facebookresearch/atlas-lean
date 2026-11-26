# The fuelled IMP evaluator on an assignment

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns either $\mathrm{some}(t)$, success with a final state $t$, or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every fuel $k$, variable index $x$, arithmetic expression $a$ and state $s$, $\operatorname{exec}(k + 1, x := a, s) = \mathrm{some}(s[x \mapsto a(s)])$, where $s[x \mapsto a(s)]$ is the state $s$ with variable $x$ set to the value of $a$ in $s$.
