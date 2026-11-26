# Beta(2−α, α) coalescent genealogy near explosion of a Galton–Watson tree

**Setting.** Let $(Z_t)_{t\in\mathbb{R}}$ be the stationary limit of the rescaled population of an explosive continuous-time Galton–Watson tree with offspring generating function $f(s) = s - (1-s)^\alpha L(1-s)$, $\alpha \in (0,1)$, observed in logarithmic time before the explosion time (see the Depends-on entry), and let $R_t = Z_{-t}$, $t \ge 0$, be its time reversal. Sample $k \ge 2$ individuals near explosion and trace their ancestry backwards: at a jump time $t$ of $R$ where $R$ loses the fraction $v_t = (R_{t-} - R_t)/R_{t-}$ of its mass, mark each current ancestral block independently with probability $v_t$ and merge all marked blocks (no change if fewer than two are marked). Call this partition-valued process $(\pi_t)_{t\ge0}$, started from singletons.

**Theorem.** Define the random clock
$$I(t) = \inf\Big\{r \ge 0 : \int_0^r \Gamma(1+\alpha)\, R_s^{1-\alpha}\,ds \ge t\Big\}.$$
Then $(\pi_{I(t)})_{t\ge0}$, in its own filtration, is a standard $\mathrm{Beta}(2-\alpha, \alpha)$-coalescent: when there are $b$ blocks, each given set of $j$ blocks merges at rate
$$\lambda_{b,j} = \int_0^1 v^{j-2}(1-v)^{b-j}\,\frac{v^{1-\alpha}(1-v)^{\alpha-1}}{\Gamma(\alpha)\Gamma(2-\alpha)}\,dv, \qquad 2 \le j \le b.$$
With the spine to explosion carried as an extra distinguished block (merging at immigration jumps of $R$ only), the same time change turns the two-type process into an explicit red/blue Beta-type coalescent.

## Expansion

Backwards in time, a downward jump of $R$ of relative size $v$ is a birth event in which a litter accounts for a fraction $v$ of the current mass, so each lineage independently descends from that litter's parent with probability $v$; this is a $\Lambda$-coalescent paintbox driven by the jumps of $R$. The Lévy measure of the non-spine jumps, $C_\alpha x u^{-1-\alpha}e^{-u}\,du$ at state $x$, turns into a jump-size density in $v = u/(x+u)$ that, after removing the state-dependent intensity $\propto R^{1-\alpha}$ by the clock $I$, is exactly $v^{-2}\mathrm{Beta}(2-\alpha,\alpha)(dv)$, the same multiple-merger coalescent that arises for $\alpha$-stable continuous-state branching processes.

## Depends on

- [Spine to explosion and gamma population size near explosion](spine-to-explosion-and-gamma-population-size-near-explosion.md)
- [The Beta-coalescent measure on the unit interval](../../coalescent-theory/multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-lambda.md)

## Sources

- Simon C. Harris, Samuel G. G. Johnston and Juan Carlos Pardo, "Behaviour near explosion in continuous-time Galton-Watson trees", arXiv:2610.01810 (2026), Definitions 2.4 and 2.6, Theorems 2.5 and 2.7, <https://doi.org/10.48550/arXiv.2610.01810>.
