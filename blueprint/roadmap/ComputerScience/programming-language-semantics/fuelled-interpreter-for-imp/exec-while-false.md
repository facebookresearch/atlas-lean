# The fuelled IMP evaluator on a while loop with a false guard

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns either $\mathrm{some}(t)$, success with a final state $t$, or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every fuel $k$, Boolean expression $b$, command $c$ and state $s$ at which $b$ is false, $\operatorname{exec}(k + 1, \mathtt{while}\ b\ \mathtt{do}\ c, s) = \mathrm{some}(s)$.
