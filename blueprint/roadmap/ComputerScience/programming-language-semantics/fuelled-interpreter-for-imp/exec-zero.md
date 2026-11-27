# The fuelled IMP evaluator fails at fuel zero

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns either $\mathrm{some}(t)$, success with a final state $t$, or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every command $c$ and state $s$, $\operatorname{exec}(0, c, s) = \bot$.
