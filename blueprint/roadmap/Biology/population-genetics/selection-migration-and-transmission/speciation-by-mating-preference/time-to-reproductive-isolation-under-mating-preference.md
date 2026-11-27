# Time to reproductive isolation under mating preference

**Setting.** Consider the stochastic two-patch, two-type birth–death–migration process $\mathbf{N}^K(t) = (N^K_{A,1}, N^K_{a,1}, N^K_{A,2}, N^K_{a,2})$ with carrying-capacity parameter $K$: in patch $i$, type $\alpha$ is born at rate $b\, n_{\alpha,i}(\beta n_{\alpha,i} + n_{\bar\alpha,i})/(n_{\alpha,i} + n_{\bar\alpha,i})$, dies at rate $(d + c(n_{\alpha,i} + n_{\bar\alpha,i})/K)\, n_{\alpha,i}$, and migrates to the other patch at rate $p\, n_{\alpha,i} n_{\bar\alpha,i}/(n_{\alpha,i} + n_{\bar\alpha,i})$, with $\beta > 1$, $0 \le d < b$, $c > 0$, $p \ge 0$. The rescaled process $\mathbf{N}^K/K$ converges on compact time intervals, in probability, to the solution of the deterministic two-patch mating-preference system, provided the initial conditions converge. Let $\zeta = (\beta b - d)/c$ and $p_0$ be as in the deterministic convergence theorem.

**Theorem (isolation time).** Suppose $\mathbf{N}^K(0)/K$ converges in probability to a deterministic $\mathbf{z}^0$ with $z^0_{A,1} > z^0_{a,1}$, $z^0_{a,2} > z^0_{A,2}$ and $(z^0_{a,1}, z^0_{A,2}) \ne (0,0)$. For $\varepsilon > 0$ let

$$
\mathcal{B}_\varepsilon = [(\zeta - \varepsilon)K, (\zeta + \varepsilon)K] \times \{0\} \times \{0\} \times [(\zeta - \varepsilon)K, (\zeta + \varepsilon)K]
$$

and $T^K_{\mathcal{B}_\varepsilon}$ its hitting time. There are constants $\varepsilon_0, C_0, m > 0$ and $V > 0$ such that if $p < p_0$ and $\varepsilon \le \varepsilon_0$,

$$
\lim_{K \to \infty} \mathbb{P}\left( \left| \frac{T^K_{\mathcal{B}_\varepsilon}}{\log K} - \frac{1}{b(\beta - 1)} \right| \le C_0 \varepsilon,\ \ \mathbf{N}^K\big(T^K_{\mathcal{B}_\varepsilon} + t\big) \in \mathcal{B}_{m\varepsilon}\ \ \forall\, t \le e^{VK} \right) = 1 .
$$

So complete reproductive isolation between patches (type $A$ only in patch 1, type $a$ only in patch 2) is reached after a time $\sim \log K / (b(\beta - 1))$, independent of the migration rate, and then persists for a time exponentially long in $K$.

**Extinction-time ingredient.** Near the isolated state, each local minority type behaves like a subcritical birth–death process with birth rate $b$ and death rate $d + c\zeta = b\beta$. For a linear birth–death process with individual rates $b \ne d$ started from $i$ individuals,

$$
\mathbb{P}_i(T_0 \le t) = \left( \frac{d\,(1 - e^{(d - b)t})}{b - d\, e^{(d - b)t}} \right)^{i},
$$

which, applied with death rate $b\beta$ and $i$ of order $\varepsilon K$, gives extinction times concentrated around $\log K / (b(\beta - 1))$.

## Depends on

- [Equilibria and reproductive isolation in the two-patch mating-preference model](equilibria-and-isolation-in-the-two-patch-mating-preference-model.md)
- [Kurtz's law of large numbers for density-dependent chains](../../../../Probability/markov-chains/density-dependent-markov-chains/kurtz-law-of-large-numbers-for-density-dependent.md)

## Proof depends on

- [Kendall's law of the linear birth–death process](../../../../Probability/branching-processes/linear-birth-death-process/prob.md)

## Expansion

The proof has three phases. First, the law of large numbers carries the process in time $O(1)$ to a neighbourhood of $(\zeta K, 0, 0, \zeta K)$, using the deterministic convergence result for $p < p_0$. Second, starting with the minority types at order $\varepsilon K$, they decay like subcritical branching processes with growth rate $-b(\beta - 1)$ up to $O(\varepsilon)$ corrections, and the explicit extinction-time law shows they vanish after $(1/(b(\beta-1)) \pm C_0\varepsilon)\log K$. Migration is already balanced in this phase, which is why $p$ does not appear. Third, once each patch is monomorphic migration stops, and large-deviation estimates keep the resident populations near $\zeta K$ for a time $e^{VK}$. The time is inversely proportional to $\beta - 1$, consistent with the absence of isolation at $\beta = 1$. The paper extends the result to $N$ patches and to patch-dependent migration.

## Sources

- Camille Coron, Manon Costa, Hélène Leman and Charline Smadi, *A stochastic model for speciation by mating preferences*, J. Math. Biol. 76(6) (2018), 1421–1463. <https://doi.org/10.1007/s00285-017-1175-9> Lemma 1.1 (large-population approximation), Theorem 3 (main result), Proposition 4.1 (extinction time of the minority types), Theorem 4 ($N$-patch generalization), Lemma A.1 (birth–death extinction times). Locators use the numbering of the preprint arXiv:1603.01027.
