# The closed testing principle

Let $\mu$ be a measure on $\Omega$, $m \in \mathbb{N}$, $\varphi(J)(\omega)$ the decisions of local tests of the intersection hypotheses $H_J$, $J \subseteq \{0, \dots, m-1\}$, and $H_0$ the set of true nulls. If the local test of $H_{H_0}$ rejects with probability at most $\alpha \in [0, \infty]$, that is $\mu(\varphi(H_0)) \le \alpha$, then the [closed testing procedure](closed-rejections.md) rejects some true null with probability at most $\alpha$:

$$\mu(R(\omega) \cap H_0 \ne \emptyset) \le \alpha.$$

Applied to every possible $H_0$, local level-$\alpha$ tests give strong control of the familywise error rate. No assumption on the dependence between local tests is made.

## Sources

- R. Marcus, E. Peritz and K. R. Gabriel, *On closed testing procedures with special reference to ordered analysis of variance*, Biometrika 63 (1976), 655–660.
