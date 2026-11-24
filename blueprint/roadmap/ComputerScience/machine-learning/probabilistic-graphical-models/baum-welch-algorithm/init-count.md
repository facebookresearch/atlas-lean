# Expected initial-state counts

Let $S$ and $O$ be finite sets, let $T$ be a natural
number, and let $x_1, \dots, x_N$ be sequences of observations in $O$. For a valid hidden Markov
model $h$ on states $S$ and observations $O$ and a state $s$, the expected number of sequences
starting in $s$ is

$$I_s = \sum_{n=1}^{N} \sum_{z \,:\, z_0 = s} p_h(z \mid x_n),$$

where $z$ ranges over the state paths $(z_0, \dots, z_T)$ in $S$ and $p_h(z \mid x_n)$ is the
posterior of $z$ given $x_n$: the path weight of $z$ and $x_n$ under $h$ divided by the total
weight of all such paths.
