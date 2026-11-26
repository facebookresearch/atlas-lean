# Zero-determinant strategies in multiplayer social dilemmas

**Multiplayer dilemma.** A group of $n \ge 2$ players repeatedly chooses to cooperate (C) or defect (D). In a round where $j$ of the other $n - 1$ players cooperate, a cooperator receives $a_j$ and a defector $b_j$, $j = 0, \dots, n-1$. The game is a social dilemma if (a) $a_{j+1} \ge a_j$ and $b_{j+1} \ge b_j$, (b) $b_{j+1} > a_j$, and (c) $a_{n-1} > b_0$. In the linear public goods game with contribution $c > 0$ and multiplication factor $1 < r < n$, $a_j = rc(j+1)/n - c$ and $b_j = rcj/n$.

**Memory-one strategies.** In the infinitely repeated game, a memory-one strategy is a vector $\mathbf p = (p_{C,n-1}, \dots, p_{C,0};\, p_{D,n-1}, \dots, p_{D,0})$, where $p_{S,j}$ is the probability of cooperating after a round in which the player used $S$ and $j$ co-players cooperated.

**Definition and theorem.** $\mathbf p$ is a *zero-determinant (ZD) strategy* if there are constants $l$, $s$ and $\phi \ne 0$ with

$$p_{C,j} = 1 + \phi\Big[(1-s)(l - a_j) - \frac{n-j-1}{n-1}\,(b_{j+1} - a_j)\Big], \qquad p_{D,j} = \phi\Big[(1-s)(l - b_j) + \frac{j}{n-1}\,(b_j - a_{j-1})\Big]$$

for all $j$. A player $i$ using such a strategy enforces, against any strategies of the co-players, the linear relation

$$\pi_{-i} = s\,\pi_i + (1-s)\,l$$

between her long-run payoff $\pi_i$ and the average payoff $\pi_{-i} = \frac{1}{n-1}\sum_{j\ne i}\pi_j$ of her co-players. The *slope* $s$ sets how co-players' payoffs track hers, the *baseline* $l$ is the common payoff when everyone uses the same ZD strategy, and $\phi$ only affects how fast payoffs converge. In the public goods game:

- proportional Tit-for-Tat, $p_{C,j} = p_{D,j} = j/(n-1)$, is the ZD strategy with $s = 1$, $\phi = 1/c$, and enforces the fair relation $\pi_{-i} = \pi_i$;
- *extortionate* strategies have $l = 0$ and $0 < s < 1$, guaranteeing $\pi_i \ge \pi_{-i}$;
- *generous* strategies have $l = rc - c$ and $0 < s < 1$, guaranteeing $\pi_i \le \pi_{-i}$;
- ALLD and ALLC are ZD strategies with $s = \frac{(n-1)r - n}{(n-1)r}$, $\phi = \frac{(n-1)r}{cn(r-1)}$ and baselines $l = 0$ and $l = rc - c$ respectively.

## Proof sketch

For $n = 2$ this is the Press–Dyson construction: the vector $\tilde{\mathbf p}$ obtained by subtracting the player's own "repeat" indicator from $\mathbf p$ is a linear combination of the payoff vectors and the all-ones vector, and any stationary distribution $v$ of the joint Markov chain satisfies $v\cdot\tilde{\mathbf p} = 0$, which reads as a linear payoff relation. With $n$ players the joint chain has $2^n$ states, but the same argument goes through with the co-players' average payoff in place of the single opponent's (Eqs. (1)–(2) of the source, which builds on the multiplayer construction of Hilbe, Wu, Traulsen and Nowak, 2014). Feasibility requires all $p_{S,j} \in [0,1]$, which restricts $(l, s, \phi)$.

## Sources

- C. Hilbe, B. Wu, A. Traulsen, M. A. Nowak, "Evolutionary performance of zero-determinant strategies in multiplayer games", Journal of Theoretical Biology (2015), <https://doi.org/10.1016/j.jtbi.2015.03.032> (PMC4425415).
