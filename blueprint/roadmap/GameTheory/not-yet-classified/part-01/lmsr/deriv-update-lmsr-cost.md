# The LMSR instantaneous price is the derivative of the cost

For a finite nonempty set of outcomes, a liquidity parameter $b > 0$ and a share vector $q$, the derivative at $0$ of $t \mapsto C_b(q + te_i)$, where $C_b(q) = b\log\sum_j e^{q_j/b}$ is the LMSR cost, is the softmax price $e^{q_i/b}/\sum_j e^{q_j/b}$ of outcome $i$.
