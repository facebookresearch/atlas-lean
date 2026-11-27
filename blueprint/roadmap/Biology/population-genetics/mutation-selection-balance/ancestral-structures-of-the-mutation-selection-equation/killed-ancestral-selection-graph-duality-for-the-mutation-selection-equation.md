# Killed ancestral selection graph duality for the mutation–selection equation

**Setting.** In the two-type haploid Moran model of size $N$, type-0 (fit) individuals reproduce at rate $1+s$ ($s \ge 0$) and type-1 (unfit) individuals at rate $1$; every individual mutates at rate $u > 0$ to type $i$ with probability $\nu_i$ ($\nu_0 + \nu_1 = 1$). Without rescaling parameters or time, the type-1 frequency converges as $N \to \infty$, uniformly on compacts in probability, to the solution of the **mutation–selection equation**

$$\frac{dy}{dt} = -s\,y(1-y) - u\nu_0\,y + u\nu_1(1-y), \qquad y(0) = y_0 \in [0,1],$$

a Riccati equation whose stable equilibrium is

$$\bar y = \frac12\Big(1 + \frac{u}{s} - \sqrt{\Big(1-\frac{u}{s}\Big)^2 + 4\nu_0\frac{u}{s}}\Big) \ (s > 0), \qquad \bar y = \nu_1 \ (s = 0).$$

**Killed ASG.** Starting from $n$ lines, each line independently branches at rate $s$, is pruned (removed) at rate $u\nu_1$, and at rate $u\nu_0$ the whole process is sent to a cemetery state $\Delta$. Let $R_r \in \mathbb{N}_0 \cup \{\Delta\}$ be its line count, with the convention $y_0^{\Delta} = 0$.

**Theorem (duality).** For all $n$, $y_0 \in [0,1]$ and $t \ge 0$,

$$y(t;y_0)^n = E\big[y_0^{R_t} \mid R_0 = n\big].$$

Consequently $(\bar y^{R_r})_{r\ge0}$ is a martingale and the equilibrium is an absorption probability:

$$\bar y = P\big(\lim_{r\to\infty} R_r = 0 \mid R_0 = 1\big).$$

**Absorption (error threshold).**

1. If $\nu_0 = 1$, $R$ is absorbed in $\Delta$ almost surely (so $\bar y = 0$).
2. If $\nu_0 \in (0,1)$, $R$ is absorbed in $\{0, \Delta\}$ almost surely.
3. If $\nu_0 = 0$ and $u < s$, $R$ is absorbed in $0$ with probability $< 1$, and otherwise $R_r \to \infty$ (so $\bar y = u/s < 1$: the fit type persists).
4. If $\nu_0 = 0$ and $u \ge s$, $R$ is absorbed in $0$ almost surely (so $\bar y = 1$: the fit type is lost).

The transition at $u = s$ for unidirectional mutation is the error threshold, seen genealogically as the line-counting process switching from transient to recurrent.

## Expansion

Read forward, a sampled individual is unfit at time $t$ exactly when all its potential ancestors in the graph are unfit at time $0$ and no beneficial mutation hits them: branching at rate $s$ adds the incoming parent of a selective event (the individual is unfit only if both potential parents are), a deleterious mutation decides the type of a line regardless of its past (prune), and a beneficial mutation decides it is fit (kill). Hence $P(\text{all } n \text{ sampled unfit}) = y(t)^n = E[y_0^{R_t}]$. Differentiating the right side gives the generator identity $\partial_t E[y_0^{R_t}] = (s y_0^2 - (s+u)y_0 + u\nu_1)\,\partial_{y_0}E[y_0^{R_t}]$, which is the ODE. At equilibrium, $\bar y^{R_r}$ is a bounded martingale that converges to $1$ on absorption in $0$ and to $0$ otherwise. Case 3 is a supercritical birth–death chain with birth rate $s$ and death rate $u$.

## Sources

- Ellen Baake, Fernando Cordero and Sebastian Hummel, "A probabilistic view on the deterministic mutation–selection equation: dynamics, equilibria, and ancestry via individual lines of descent", *J. Math. Biol.* 77(3) (2018), 795–820. <https://doi.org/10.1007/s00285-018-1228-8>
- Preprint version (the locators in this item follow its numbering): Ellen Baake, Fernando Cordero and Sebastian Hummel, "A probabilistic view on the deterministic mutation–selection equation: dynamics, equilibria, and ancestry via individual lines of descent", arXiv:1710.04573 (2017), Section 2 (Eq. for the deterministic limit and stable equilibrium), Section 4 (Definition 1, Theorem 2, Corollary 4, Lemma 5, Corollary 6, Proposition 7), <https://doi.org/10.48550/arXiv.1710.04573>.
