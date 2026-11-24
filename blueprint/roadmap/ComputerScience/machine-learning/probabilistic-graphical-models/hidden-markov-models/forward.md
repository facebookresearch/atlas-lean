# Forward variables of a hidden Markov model

Let $h$ be a hidden Markov model with a finite
set of states $S$ and weights in a semiring $R$, with initial weights $\pi(s)$, transition weights
$a(s', s)$ from $s'$ to $s$ and emission weights $e(s, o)$ of the observation $o$ from the state
$s$, and let $x$ be an observation sequence. The forward variables are defined by
$\alpha_0(s) = \pi(s) \, e(s, x_0)$ and
$\alpha_{t+1}(s) = \left(\sum_{s'} \alpha_t(s') \, a(s', s)\right) e(s, x_{t+1})$, the sum
running over all states $s'$.

The forward variable $\alpha_t(s)$ is the weight of the observations $x_0, \dots, x_t$ with the
state at time $t$ equal to $s$.
