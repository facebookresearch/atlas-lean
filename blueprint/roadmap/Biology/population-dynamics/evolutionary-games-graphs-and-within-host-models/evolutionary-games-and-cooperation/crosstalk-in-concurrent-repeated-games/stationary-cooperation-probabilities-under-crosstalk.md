# Stationary cooperation probabilities under crosstalk

Consider $N$ players, each pair $i \ne j$ meeting to play one round of a repeated two-action game
with probability $w_{ij} = w_{ji} \ge 0$ per round, where $w_{ii} = 0$ and
$\sum_{i<j} w_{ij} = 1$; write $\bar w_i = \sum_{j=1}^N w_{ij}$ for the probability that the next
round involves player $i$. Each player $i$ uses a reactive strategy $(p_i, q_i) \in [0,1]^2$ and
keeps, for every co-player, an automaton whose state is $C$ or $D$: after a round the state towards
that co-player becomes $C$ with probability $p_i$ if the co-player cooperated and with probability
$q_i$ if it defected. **Crosstalk** of rate $\gamma \in [0,1]$ means that, when a round is played,
each player acts with probability $1 - \gamma$ on the state held towards the current co-player and
with probability $\gamma$ on the state updated in its own previous round, against whoever that
co-player was.

Let $y_{ij}^t$ be the probability that player $i$ is in state $C$ towards player $j$ at time $t$,
and $y_i^t$ the probability that $i$ is in state $C$ towards its previous co-player. Then

$$y_{ij}^{t+1} = (1 - w_{ij})\,y_{ij}^t
 + (1-\gamma)\,w_{ij}\bigl(y_{ji}^t p_i + (1 - y_{ji}^t) q_i\bigr)
 + \gamma\,w_{ij}\bigl(y_{j}^t p_i + (1 - y_{j}^t) q_i\bigr).$$

Assume every player takes part in some interaction, $\bar w_i > 0$ for all $i$, so that
$w_{ik}/\bar w_i$ is defined. In a steady state, $y_{ij}^{t+1} = y_{ij}^t =: y_{ij}$ and
$y_i = \sum_{k=1}^N (w_{ik}/\bar w_i)\, y_{ik}$. For every ordered pair $(i,j)$ with $w_{ij} > 0$,
subtracting $(1 - w_{ij})\,y_{ij}$ and dividing by $w_{ij}$ shows that the stationary cooperation
probabilities solve the inhomogeneous linear system

$$y_{ij} - (1-\gamma)(p_i - q_i)\,y_{ji} - \gamma\,(p_i - q_i)\,y_j = q_i
\qquad (i \ne j,\ w_{ij} > 0).$$

There is one equation for each ordered pair that meets with positive probability, $N(N-1)$ in
total exactly when all $w_{ij} > 0$ for $i \ne j$ (for example the complete graph). If
$w_{ij} = 0$, the recursion reads $y_{ij}^{t+1} = y_{ij}^t$: the state of $i$ towards $j$ never
changes, every value of $y_{ij}$ is stationary, and that pair contributes no equation. Such
$y_{ij}$ also never enter the system: $y_i$ weights $y_{ik}$ by $w_{ik}$, and the equation for
$(j,i)$ is absent as well because $w_{ji} = w_{ij} = 0$.

The source states that "the Eqs. (2) represent a system of $N(N-1)$ linear equations in the
unknowns $y_{ij}$ with $i \ne j$", while its own examples (such as the cycle) set $w_{ij} = 0$ for
non-neighbours. Its Eq. (2) is obtained from Eq. (1) by dividing by $w_{ij}$, which is valid only
when $w_{ij} > 0$, and its definition of $y_i$ divides by $\bar w_i$; this page therefore adds the
requirements $w_{ij} > 0$ for each equation and $\bar w_i > 0$ for each player.

## Remarks

At $\gamma = 0$ the system decouples into independent pairs and reproduces standard direct
reciprocity, where $y_{ij}$ depends only on the pair $(i,j)$. For $\gamma > 0$ every game is
coupled to every other game the two players take part in, so one defection can propagate through
the interaction network; a player using Tit-for-Tat ($p = 1$, $q = 0$) transmits such a cascade
without damping, whereas generous Tit-for-Tat ($p = 1$, $0 < q < 1$) contracts it.

## Sources

- J. G. Reiter, C. Hilbe, D. G. Rand, K. Chatterjee, M. A. Nowak, "Crosstalk in concurrent repeated
  games impedes direct reciprocity and requires stronger levels of forgiveness",
  Nature Communications 9 (2018) 555, Methods, "Analytical derivation of steady-state payoffs", Eqs. (1) and (2),
  <https://doi.org/10.1038/s41467-017-02721-8> (PMC5803203).
