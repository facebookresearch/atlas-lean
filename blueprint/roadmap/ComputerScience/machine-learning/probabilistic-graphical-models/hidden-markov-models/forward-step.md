# One step of the tabulated forward algorithm

Let $h$ be a hidden Markov model with states
$\{0, \dots, n-1\}$ and weights in a semiring $R$, with transition weight $a(s', s)$ from $s'$ to
$s$ and emission weight $e(s, o)$ of the observation $o$ from the state $s$, and let $x$ be an
observation sequence. For a table $v \in R^n$ and a step $t$, the forward step returns the table
whose entry at a state $s$ is

$$\Bigl(\sum_{s'=0}^{n-1} v_{s'} \, a(s', s)\Bigr) \, e(s, x_{t+1}).$$
