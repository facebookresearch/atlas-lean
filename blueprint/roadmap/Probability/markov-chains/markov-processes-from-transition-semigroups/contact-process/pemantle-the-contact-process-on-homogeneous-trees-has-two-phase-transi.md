# The contact process on homogeneous trees has at least two phase transitions

Let $T$ be the homogeneous tree in which every vertex has $n + 1$ neighbours, and run the contact process on $T$: infected vertices recover at rate $1$ and infect each neighbour at rate $\lambda$. Write $\xi(t)$ for the set of infected vertices, $\rho$ for the root and $P^\rho$ for the law started from $\rho$ alone. Pemantle (1992, Definition 1.1) defines the critical values $\lambda_1 = \inf\{\lambda : P^\rho(\xi(t) \ne \emptyset \text{ for all } t) > 0\}$ for global survival, $\lambda_a = \inf\{\lambda : P^\rho(\rho \in \xi(t) \text{ for arbitrarily large } t) > 0\}$, $\lambda_b = \inf\{\lambda : \limsup_{t\to\infty} P^\rho(\rho \in \xi(t)) > 0\}$ and $\lambda_2 = \inf\{\lambda : \liminf_{t\to\infty} P^\rho(\rho \in \xi(t)) > 0\}$, with $\lambda_1 \le \lambda_a \le \lambda_b \le \lambda_2$. His Theorem 2.1 states that for all $n > 2$, $0 < \lambda_1 < \lambda_2 < \infty$, and that for $n = 2$ the same holds except that the middle inequality may fail to be strict. It is a consequence of Theorem 2.2, whose explicit bounds on $\lambda_1$ and $\lambda_a$ give $\lambda_1 < \lambda_a$ for $n > 2$. Hence for $n > 2$ and $\lambda_1 < \lambda < \lambda_a$ there is weak survival: the process started from one infected vertex survives with positive probability, while almost surely the root is infected only at bounded times.

## Proof depends on

- [Poisson process](../../../point-processes/poisson-processes/is-poisson-process.md)
- [Optional stopping for supermartingales at a bounded stopping time](../../../../Probability/martingales/optional-stopping-theorem/expected-stopped-value-le.md): on the stopped jump chain, with bounded truncation

## Expansion

1. The model: the graphical construction of the contact process on $T$, monotonicity, and the definitions of $\lambda_1$, $\lambda_a$, $\lambda_b$, $\lambda_2$ (Definition 1.1) and the inequalities between them.
2. Bounds on $\lambda_1$ (Theorem 2.2 (i)–(ii)) from comparison with branching random walks and a supermartingale argument.
3. Bounds on $\lambda_a$ (Theorem 2.2 (iii)–(iv)), giving $\lambda_1 < \lambda_a$ for $n > 2$, and with $\lambda_a \le \lambda_b \le \lambda_2$ the separation $\lambda_1 < \lambda_2$ of Theorem 2.1.
4. The case $n = 2$, completed by later work (Liggett; Stacey), as a separate statement.

## Sources

- R. Pemantle, The contact process on trees, Ann. Probab. 20 (1992), 2089–2116, Theorems 2.1 and 2.2. <https://doi.org/10.1214/aop/1176989541> (arXiv: <https://arxiv.org/abs/math/0404046>)
