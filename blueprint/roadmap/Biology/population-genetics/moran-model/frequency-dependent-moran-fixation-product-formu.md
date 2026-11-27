# Fixation probability in a frequency-dependent Moran process

Consider a birth–death Markov chain on $\{0, 1, \dots, N\}$, absorbing at $0$ and $N$, that from state $i$ (the number of
mutants) moves up with probability $\alpha_i > 0$ and down with probability $\beta_i > 0$, $\alpha_i + \beta_i \le 1$, for $1 \le i \le N - 1$ (and otherwise stays), and let
$\gamma_i = \beta_i / \alpha_i$. Then the probability that a single mutant reaches fixation is

$$\rho = \frac{1}{1 + \sum_{k=1}^{N-1} \prod_{i=1}^k \gamma_i} .$$

In the Moran process with positive frequency-dependent fitnesses $f_i$ of mutants and $g_i$ of residents in state $i$
(one birth proportional to fitness, then one uniform death),
$\alpha_i = \frac{i f_i}{i f_i + (N - i) g_i} \cdot \frac{N - i}{N}$ and $\beta_i = \frac{(N - i) g_i}{i f_i + (N - i) g_i} \cdot \frac iN$, so
$\gamma_i = g_i / f_i$. For constant relative fitness $f_i = r$, $g_i = 1$ with $r > 0$, $r \ne 1$, this gives
$\rho = (1 - 1/r)/(1 - r^{-N})$, the [Moran fixation probability](moran-fixation.md), and $r = 1$ gives $\rho = 1/N$. The formula follows because $x_i = \mathbb P_i[\text{fixation}]$
satisfies $x_{i+1} - x_i = \gamma_i (x_i - x_{i-1})$ with $x_0 = 0$, $x_N = 1$.

## Depends on

- [Fixation probability of the Moran process](moran-fixation.md)

## Sources

- M. A. Nowak, A. Sasaki, C. Taylor and D. Fudenberg, "Emergence of cooperation and evolutionary stability in finite populations", Nature 428 (2004), 646–650, <https://doi.org/10.1038/nature02414>. The formula is derived above.
