# Steady-state payoffs under crosstalk

In the donation game, a cooperating player pays cost $c > 0$ so that its co-player receives benefit
$b > c$. With the notation and the stationary cooperation probabilities $\hat y_{ij}$ of the
crosstalk model, and $\hat y_j = \sum_{k} (w_{jk}/\bar w_j)\,\hat y_{jk}$, the long-run payoff of
player $i$ is

$$\pi_i = \sum_{j=1}^{N} \frac{w_{ij}}{\bar w_i}
\Bigl[\bigl((1-\gamma)\,\hat y_{ji} + \gamma\,\hat y_j\bigr) b - \hat y_{ij}\, c\Bigr].$$

The first term is the benefit $i$ receives, in which the co-player $j$ acts on its state towards
$i$ with probability $1 - \gamma$ and on the state towards its previous partner with probability
$\gamma$; the second term is the cost $i$ pays for its own cooperation.

## Depends on

- [Stationary cooperation probabilities under crosstalk](stationary-cooperation-probabilities-under-crosstalk.md)

## Remarks

Because the payoffs are linear functionals of the solution of a linear system, they can be computed
for arbitrary population structures, arbitrary crosstalk rates and arbitrary mixtures of reactive
strategies. Feeding $\pi_i$ into an imitation process with imitation probability
$\rho = [1 + e^{-s(\pi_R - \pi_L)}]^{-1}$ gives the evolutionary dynamics of the strategies
themselves, with the separation of timescales that treats stationary payoffs as fitnesses.

## Sources

- J. G. Reiter, C. Hilbe, D. G. Rand, K. Chatterjee, M. A. Nowak, "Crosstalk in concurrent repeated
  games impedes direct reciprocity and requires stronger levels of forgiveness",
  Nature Communications 9 (2018) 555, Eq. (3),
  <https://doi.org/10.1038/s41467-017-02721-8> (PMC5803203).
