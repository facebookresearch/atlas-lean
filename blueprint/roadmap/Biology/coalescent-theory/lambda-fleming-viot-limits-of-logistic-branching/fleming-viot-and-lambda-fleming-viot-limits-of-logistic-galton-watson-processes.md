# Fleming–Viot and Λ-Fleming–Viot limits of logistic Galton–Watson processes

**Model.** In a continuous-time Bienaymé–Galton–Watson process with logistic competition, each individual reproduces at rate $b$, producing $k \ge 1$ offspring with probability $p_k$, and dies at rate $d + c_K N$, where $N$ is the current population size and $c_K = c/K$ (carrying capacity of order $K$). Individuals carry neutral labels inherited by their offspring; $\rho^K_t$ is the empirical label distribution. Assume $bm > d$ where $m = \sum_k kp_k$, and let $n_* = (bm - d)/c$.

**Theorem.** Suppose the label distribution at time $0$ converges in probability to $\rho_0$.
1. *(Finite variance.)* If $\sum_k k^{2+\delta}p_k < \infty$ for some $\delta > 0$ and $N/K \to n_*$ initially, then on time scale $Kt$ the rescaled size $N/K$ stays uniformly close to $n_*$ on $[0, T]$, and $(\rho^K_{Kt})_{t \le T}$ converges in distribution in $D([0, T])$ to a Fleming–Viot diffusion with speed $1/N_e$, where
$$N_e = \frac{n_*}{b\,(m + m_{(2)})}, \qquad m_{(2)} = \sum_k k^2 p_k.$$
2. *(α-stable offspring.)* If $p_k \sim p_0 k^{-1-\alpha}$ with $\alpha \in (1, 2)$ and $N/K$ is initially tight in $(0, \infty)$, then on time scale $K^{\alpha-1}t$ the size $N/K$ spends almost all time near $n_*$, and $\rho^K$ converges to the $\Lambda$-Fleming–Viot process with
$$\Lambda(du) = \frac{b\,p_0\,\alpha}{n_*^{\alpha-1}}\,(1-u)^{\alpha-1}u^{1-\alpha}\,du,$$
a multiple of the Beta$(2-\alpha, \alpha)$ measure.
3. *(Neveu regime.)* If $k^2 p_k \to p_0$, then with $n_* = bp_0/c$ the size rescaled by $K\log K$ concentrates near $n_*$, and on the original time scale $\rho^K$ converges to the $\Lambda$-Fleming–Viot process with $\Lambda(du) = b\,p_0\,du$, the dual of the Bolthausen–Sznitman coalescent.

## Depends on

- [The Beta-coalescent measure on the unit interval](../../coalescent-theory/multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-lambda.md)

## Expansion

Competition is fast relative to the label dynamics: the population size relaxes to its quasi-equilibrium $n_* K$ on time scale $O(1)$, while label frequencies move on the slow scale set by reproductive variance. A stochastic averaging principle (Kurtz) replaces the fast size process by its equilibrium. With finite offspring variance, each birth event shifts frequencies by $O(1/K)$, giving a diffusion with effective size $N_e$. With heavy-tailed litters, a single birth of $yK$ offspring occurs at rate about $b n_* p_0 K^{1-\alpha}y^{-\alpha}/\alpha$, and competition then thins all labels equally, acting like Schweinsberg's sampling step; these macroscopic jumps produce the Beta-type multiple mergers in the dual genealogy.

## Sources

- R. Forien, "Lambda-Fleming-Viot processes arising in logistic Bienaymé-Galton-Watson processes with a large carrying capacity", arXiv:2501.16837 (2025), main theorems of Sections 1.1–1.3 (finite variance, α-stable and Neveu regimes), <https://doi.org/10.48550/arXiv.2501.16837>.
