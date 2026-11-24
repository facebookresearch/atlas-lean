# The fuelled IMP evaluator on skip

Let $\operatorname{exec}(k, c, s)$ be the fuelled IMP evaluator, which returns a final state or failure $\bot$; at fuel $k + 1$ every recursive call, including both parts of a sequence and the body and the repeated loop of a while, receives fuel $k$. For every fuel $k$ and state $s$, $\operatorname{exec}(k + 1, \mathtt{skip}, s) = s$.
