# Critical benefit-to-cost ratio with game transitions

**Model.** $N$ players occupy the nodes of a $k$-regular graph and are either cooperators ($C$) or defectors ($D$). Every edge carries a game state $i \in \{1, \dots, n\}$; game $i$ is a donation game in which a cooperator pays $c > 0$ to give its partner $b_i > c$, so that $R_i = b_i - c$, $S_i = -c$, $T_i = b_i$, $P_i = 0$, and game $1$ is the most valuable, $b_1 \ge b_i$ for all $i$. In each time step every player plays the current game with each neighbor, accumulates payoff $\pi$, and has fitness $f = 1 - \delta + \delta\pi$ with selection intensity $0 < \delta \ll 1$. Afterwards the game on each edge moves from state $i$ to state $j$ with probability $p_{ij}(s)$, where $s \in \{0,1,2\}$ is the number of cooperators in that pair ("global" transitions: every edge may update in every step). Strategies are updated by death–birth, birth–death or pairwise-comparison updating. Write $\rho_C$ and $\rho_D$ for the fixation probabilities of a single randomly placed cooperator and defector, and $\Delta b_{1i} = b_1 - b_i$.

**Hypotheses on the transitions.** For each $s \in \{0,1,2\}$ the chain on $\{1,\dots,n\}$ with transition matrix $P(s) = (p_{ij}(s))$ has a single aperiodic recurrence class, with stationary distribution $u(s) = (u_1(s), \dots, u_n(s))$, $u(s) = u(s)P(s)$, $\sum_j u_j(s) = 1$.

**Result.** Under weak selection and $N \gg k$:

- death–birth updating:

$$\rho_C > \rho_D \iff \frac{b_1}{c} > k - \sum_{i=2}^{n} \xi_i\,\frac{\Delta b_{1i}}{c}, \qquad \xi_i = \frac{k-1}{2}\,u_i(1) - \frac{k+1}{2}\,u_i(2);$$

- birth–death or pairwise-comparison updating:

$$\rho_C > \rho_D \iff \sum_{i=2}^{n} \xi_i\,\frac{\Delta b_{1i}}{c} > 1, \qquad \xi_i = \frac{u_i(1) - u_i(2)}{2}.$$

The coefficients $\xi_i$ depend only on the transition pattern, not on $b_i$ or $c$. For two states,

$$u_2(s) = \frac{p_{12}(s)}{p_{12}(s) + p_{21}(s)} .$$

**Special cases.**

- Mutual cooperation leads to game $1$ and every other outcome to game $2$: $\xi = (k-1)/2$ under death–birth, giving $b_1/c > k - \xi\,\Delta b/c$ with $\Delta b = b_1 - b_2$, and $\xi = 1/2$ under birth–death and pairwise comparison, giving $\xi\,\Delta b/c > 1$, i.e. $b_1 - b_2 > 2c$.
- State-independent transitions to game $2$ with probability $p$ after mutual cooperation and $q$ after unilateral cooperation: $\xi = \frac{k-1}{2}\,q - \frac{k+1}{2}\,p$ (death–birth).
- $b_1 = b_2$ (a single game): the correction vanishes and the classical rule $b/c > k$ is recovered under death–birth, while under birth–death and pairwise comparison cooperation is never favored.

Consequently, if mutual cooperation steers the pair toward the more valuable game and defection away from it, cooperation can be favored even when each game separately disfavors it ($b_1/c < k$ and $b_2/c < k$), and a small payoff difference $\Delta b$ between games is multiplied by a factor of order $k$.

## Proof sketch

Under weak selection the comparison $\rho_C > \rho_D$ reduces to a condition that is linear in the payoffs of the games, with coefficients computed from the neutral process. Since game states respond to the strategy pair on each edge, the payoff a cooperator collects depends on how often its mutual-cooperation edges ($s = 2$) and its mixed edges ($s = 1$) are in each game; under the stated recurrence hypothesis these frequencies are the stationary weights $u_i(2)$ and $u_i(1)$. Writing $b_i = b_1 - \Delta b_{1i}$ separates the condition into the static term ($b_1/c > k$ for death–birth) plus a correction $\sum_i \xi_i\,\Delta b_{1i}/c$, in which $\xi_i$ carries the transition pattern and $\Delta b_{1i}$ the variation between games. The two factors are independent, so the effect of a transition rule can be computed once and combined with any choice of benefits. The full derivation, including transition rules whose outcome depends on the initial game frequencies, is in the paper's supplementary information.

## Sources

- Q. Su, A. McAvoy, L. Wang, M. A. Nowak, "Evolutionary dynamics with game transitions", Proceedings of the National Academy of Sciences USA 116(51) (2019) 25398–25404, Eqs. 1–5 and Materials and Methods ("Calculation of $\xi_i$"), <https://doi.org/10.1073/pnas.1908936116> (PMC6926053).
