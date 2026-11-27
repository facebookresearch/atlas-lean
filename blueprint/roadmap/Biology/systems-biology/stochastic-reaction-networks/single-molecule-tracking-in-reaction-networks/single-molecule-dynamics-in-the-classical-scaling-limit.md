# Single-molecule dynamics in the classical scaling limit of reaction networks

**Setting.** A stochastic reaction network on $d$ species has reactions $y \to y'$ (complexes $y, y' \in \mathbb{Z}^d_{\ge 0}$) and a volume parameter $V$; the copy-number process $X^V$ jumps by $y' - y$ at rate $\lambda^V_{y\to y'}(X^V)$. Under the classical (density-dependent) scaling assumption $\lambda^V_{y\to y'}(\lfloor Vz\rfloor)/V \to \lambda_{y \to y'}(z)$ locally uniformly with locally Lipschitz limits, Kurtz's law of large numbers gives $X^V/V \to Z$ uniformly on compact time intervals in probability, where $\dot Z = \sum_{y\to y'}\lambda_{y\to y'}(Z)(y' - y)$.

**Tracking a molecule.** Let $\mathcal{T}$ be a finite set of statuses of one tagged molecule (which species it currently belongs to, possibly with extra history such as "has been phosphorylated"), with $\sigma(S)$ the species of status $S$ and a cemetery status $\Delta$ for a molecule that has left the system. When a reaction $y \to y'$ fires and involves the tagged molecule (chosen uniformly among the $y_{\sigma(S)}$ consumed molecules of its species), the status moves from $S$ to $S'$ with probability $p_{y\to y'}(S, S')$. The pair $(Y^V, X^V)$ is a Markov chain, the *tracking stochastic reaction system*.

**Theorem.** Assume the classical scaling, $X^V(0)/V \to z^* \in \mathbb{R}^d_{>0}$, that $Z$ exists on $[0, T]$ with $\min_{i,\,u \le T} Z_i(u) > 0$, and $Y^V(0) = Y(0)$. Let $Y$ be the time-inhomogeneous Markov chain on $\mathcal{T}$ that jumps from $S$ to $S'$ through reaction $y \to y'$ at rate

$$\lambda_{S + y \to S' + y'}(S, Z(t)) = p_{y\to y'}(S, S')\, y_{\sigma(S)}\,\frac{\lambda_{y\to y'}(Z(t))}{Z_{\sigma(S)}(t)}.$$

1. $\lim_{V\to\infty}\sup_{t \le T}\mathbb{P}(Y^V(t) \ne Y(t)) = 0$ under the natural coupling, with explicit non-asymptotic error bounds.
2. $Y^V \to Y$ in probability as processes in $D_{\mathcal{T}}[0, T]$.
3. *(Reconstruction from independent molecules.)* If for every reaction $y\to y'$ and every status $\tau'\ne\Delta$, $\sum_{\tau\ne\Delta}y_{\sigma(\tau)}\,p_{y\to y'}(\tau,\tau')=y'_{\sigma(\tau')}$ (Assumption 5.1 of the source), and the initial number of molecules of the tracked species has finite mean, then the empirical aggregate $\widetilde X^V(t)$ (the source's (5.6)) built from $\lfloor Vz^*\rfloor$ independent copies of $Y$, started from the initial composition, satisfies $\lim_V \mathbb{E}\big[\sup_{s \le t}\|X^V(s)/V - \widetilde X^V(s)/V\|\big] = 0$ for the tracked species.

## Depends on

- [Kurtz's law of large numbers for density-dependent reaction networks](../../../../Chemistry/chemical-kinetics/kurtz-s-law-of-large-numbers-for-reaction-networ/tendsto-measure-deviation.md)

## Expansion

In a large system one molecule of species $i$ sees the rest of the population as a deterministic environment $Z(t)$: a reaction consuming $y_i$ molecules of species $i$ fires at rate about $V\lambda_{y\to y'}(Z)$ among about $VZ_i$ candidates, so a given molecule participates at rate $y_i\lambda_{y\to y'}(Z)/Z_i$. The tagged molecule thus follows a Markov chain driven by the mean-field ODE, a propagation-of-chaos statement for chemistry. This makes single-molecule observables computable without simulating the full system: residence-time distributions in each species, the number of times a molecule is modified, or the fate of an infected individual in an SIS epidemic written as a reaction network.

## Sources

- Daniele Cappelletti and Grzegorz A. Rempala, "Individual Molecules Dynamics in Reaction Network Models", SIAM Journal on Applied Dynamical Systems 22 (2023), 1344–1382, <https://doi.org/10.1137/21m1459563>; numbering as in arXiv:2111.08559: Theorem 3.1, Definition 4.1, Lemma 5.1, Theorems 5.2, 5.3 and 5.5, Theorem A.2.
