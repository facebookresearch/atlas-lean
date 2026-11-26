# The fuelled IMP evaluator fails on a while loop whose body fails

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns either $\mathrm{some}(t)$, success with a final state $t$, or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every fuel $k$, Boolean expression $b$, command $c$ and state $s$ at which $b$ is true, if $\operatorname{exec}(k, c, s) = \bot$, then $\operatorname{exec}(k + 1, \mathtt{while}\ b\ \mathtt{do}\ c, s) = \bot$.
