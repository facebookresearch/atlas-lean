# Expected privacy loss

For probability mass functions $P, Q$ on a type $\Omega$, the expected privacy loss is the real number

$$
\sum_{w \in \Omega} P(w)\, L_{P\|Q}(w),
$$

the $P$-expectation of the [privacy loss](privacy-loss.md), with the sum read as $0$ when it does not converge. Because the loss is $0$ off the common support, an outcome charged by $P$ but not by $Q$ contributes $0$.

The comparison with the Kullback–Leibler divergence of the induced measures needs assumptions on the measurable space. If singletons of $\Omega$ are measurable, such an outcome makes $\mathrm{KL}(P \| Q)$ infinite, while the expected privacy loss stays finite; if moreover $\Omega$ is countable, the two agree under two-sided pointwise bounds between $P$ and $Q$. Without measurable singletons the induced measures can coincide for different $P, Q$: on a two-point space with the trivial σ-algebra, two different point masses induce the same measure, whose Kullback–Leibler divergence is $0$.
