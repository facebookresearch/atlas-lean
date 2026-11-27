# Expected emission counts

Let $S$ and $O$ be finite sets, let $T$ be a natural number,
and let $x_1, \dots, x_N$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$.
For a valid hidden Markov model $h$ on states $S$ and observations $O$, a state $s$ and an
observation $o$, the expected number of emissions of $o$ from $s$ is

$$E_{so} = \sum_{n=1}^{N} \sum_{z} p_h(z \mid x_n) \, \#\{t \le T : z_t = s,\ x_{n,t} = o\},$$

where $z$ ranges over the state paths $(z_0, \dots, z_T)$ in $S$ and $p_h(z \mid x_n)$ is the
posterior of $z$ given $x_n$: the path weight of $z$ and $x_n$ under $h$ divided by the total
weight of all such paths.
