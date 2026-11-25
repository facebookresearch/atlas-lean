# Holley's coupling theorem

Let $E$ be a finite set and $\mu_1, \mu_2 : \{0,1\}^E \to \mathbb{R}$ strictly positive probability mass functions ($\mu_i > 0$, $\sum_\omega \mu_i(\omega) = 1$) satisfying the Holley lattice condition

$$\mu_1(a)\,\mu_2(b) \le \mu_1(a \wedge b)\,\mu_2(a \vee b) \quad \text{for all } a, b \in \{0,1\}^E.$$

Let $m_i = \sum_\omega \mu_i(\omega)\,\delta_\omega$. Then there is a finite measure $\kappa$ on $\{0,1\}^E \times \{0,1\}^E$ that is a monotone coupling of $m_1$ and $m_2$: its marginals are $m_1$ and $m_2$ and it gives no mass to the pairs $(a, b)$ with $a \not\le b$.

## Sources

- R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974), 227–231.
- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, Chapter 2.
