# The fuelled IMP evaluator on a conditional with a false guard

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns either $\mathrm{some}(t)$, success with a final state $t$, or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every fuel $k$, Boolean expression $b$, commands $c_1, c_2$ and state $s$ at which $b$ is false, $\operatorname{exec}(k + 1, \mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, s) = \operatorname{exec}(k, c_2, s)$.
