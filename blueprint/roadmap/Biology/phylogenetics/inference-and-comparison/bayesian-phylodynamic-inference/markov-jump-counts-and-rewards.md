# Markov jump counts and rewards

Let $(X_s)_{s \ge 0}$ be a continuous-time Markov chain on a finite state set $S$ with rate matrix $Q = (q_{ab})$ (off-diagonal entries nonnegative, rows summing to zero) and transition matrix $P(t) = e^{Qt}$. For distinct states $a \ne b$ let $N_{ab}(t)$ be the number of jumps from $a$ to $b$ during $[0,t]$ (a **Markov jump** count), and for a state $a$ let $R_a(t) = \int_0^t \mathbf 1[X_s = a]\,ds$ be the time spent in $a$ (a **Markov reward**).

**Theorem.** For all $i, j \in S$ and $t \ge 0$,

$$\mathbb{E}\big[N_{ab}(t)\,\mathbf 1[X_t = j] \mid X_0 = i\big] = q_{ab} \int_0^t P_{ia}(s)\, P_{bj}(t-s)\, ds,$$

$$\mathbb{E}\big[R_a(t)\,\mathbf 1[X_t = j] \mid X_0 = i\big] = \int_0^t P_{ia}(s)\, P_{aj}(t-s)\, ds .$$

Dividing by $P_{ij}(t)$ (when positive) gives the expected number of $a \to b$ jumps, and the expected time in $a$, along a branch of length $t$ conditional on its end states. In matrix form, the first quantity is the $(i,j)$ entry of $q_{ab}\int_0^t e^{Qs} E_{ab}\, e^{Q(t-s)}\, ds$, where $E_{ab}$ is the matrix unit.

## Depends on

- [Site likelihood of a phylogenetic tree](../../felsenstein-s-pruning-algorithm/likelihood.md)

## Proof sketch

The process $N_{ab}(t) - q_{ab} R_a(t)$ is a martingale (the jump counting process has intensity $q_{ab}\mathbf 1[X_{s^-} = a]$). Hence the probability that an $a \to b$ jump occurs in $[s, s+ds]$ is $P_{ia}(s)\,q_{ab}\,ds$, after which the chain restarts from $b$ by the strong Markov property and reaches $j$ at time $t$ with probability $P_{bj}(t-s)$; integrating over $s$ gives the first formula, and the second is the same computation with the occupation indicator. On a phylogeny, branch-wise expectations conditional on the observed tip states are obtained by combining these end-state-conditioned quantities with the partial likelihoods of the pruning algorithm, and summing over branches. Bayesian phylodynamic software uses these quantities to date and count trait changes (for example, migration events between locations) and to map synonymous and non-synonymous substitutions for site-specific $d_N/d_S$, integrating over the posterior distribution of trees.

## Sources

- M. A. Suchard, P. Lemey, G. Baele, D. L. Ayres, A. J. Drummond and A. Rambaut, "Bayesian phylogenetic and phylodynamic data integration using BEAST 1.10", Virus Evolution 4 (2018) vey016, Section 2 ("Data integration", Markov jumps and Markov rewards), <https://doi.org/10.1093/ve/vey016>, PMCID PMC6007674.
- V. N. Minin and M. A. Suchard, "Counting labeled transitions in continuous-time Markov models of evolution", Journal of Mathematical Biology 56 (2008) 391–412.
