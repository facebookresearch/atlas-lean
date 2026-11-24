# Tabulated forward-backward smoothing

Let $g$ be a hidden Markov model with states
$\{0, \dots, n - 1\}$ and weights in a semifield $K$, and let $x_0, x_1, \dots$ be observations.
For $t, k \in \mathbb{N}$, this is the vector in $K^n$ whose entry at state $s$ is
$\alpha_t(s)\, \beta_k(t, s) / L_{t+k}$, where $\alpha_t$ is the tabulated forward vector at time
$t$, $\beta_k(t, \cdot)$ is the tabulated backward vector for $k$ steps from time $t$, and $L_{t+k}$
is the tabulated likelihood of $x_0, \dots, x_{t+k}$.

Its entries are the smoothing weights of all states at time $t$, computed in $O((t + k) n^2)$
operations.
