# q-value is at most the pFDR of the smallest region

Let $\mathrm{pfdr} : \mathbb{R} \to \mathbb{R}$ be nonnegative. For every $t \in \mathbb{R}$, the [q-value](q-value.md) satisfies $q(t) \le \mathrm{pfdr}(t)$: it is at most the pFDR of the smallest region $\{T \le t\}$ containing the statistic.
