# Expected privacy loss

For probability mass functions $P, Q$ on a type $\Omega$, the expected privacy loss is the real number

$$
\sum_{w \in \Omega} P(w)\, L_{P\|Q}(w),
$$

the $P$-expectation of the [privacy loss](privacy-loss.md), with the sum read as $0$ when it does not converge. Because the loss is $0$ off the common support, an outcome charged by $P$ but not by $Q$ contributes $0$, whereas the Kullback–Leibler divergence $\mathrm{KL}(P \| Q)$ is then infinite; the two agree under two-sided pointwise bounds between $P$ and $Q$.
