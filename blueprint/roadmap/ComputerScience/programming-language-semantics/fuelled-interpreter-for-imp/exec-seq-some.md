# The fuelled IMP evaluator on a sequence whose first part succeeds

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns either $\mathrm{some}(t)$, success with a final state $t$, or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every fuel $k$, commands $c_1, c_2$ and states $s, m$, if $\operatorname{exec}(k, c_1, s) = \mathrm{some}(m)$, then $\operatorname{exec}(k + 1, c_1 ; c_2, s) = \operatorname{exec}(k, c_2, m)$.
