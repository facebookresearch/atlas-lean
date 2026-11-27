# Number of visits to a state before step $n$

Let $S$ be a set, $x_0, x \in S$, $\omega$ a step sequence ($\omega_j = (\xi_j, E_j)$ with
$\xi_j : S \to S$ and $E_j \in \mathbb{R}$) and $n \in \mathbb{N}$. The number of visits to $x_0$
before step $n$ of the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y$ started at $x$ is

$$N_n(x_0, x, \omega) = \#\{\, j < n : Y_j(x, \omega) = x_0 \,\} ,$$

the number of steps $j \in \{0, \dots, n - 1\}$ at which the chain is at $x_0$. Step $0$ counts
when $x = x_0$, and $N_0 = 0$.
