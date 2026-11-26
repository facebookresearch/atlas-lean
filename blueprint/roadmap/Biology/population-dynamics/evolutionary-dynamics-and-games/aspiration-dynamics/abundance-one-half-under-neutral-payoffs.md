# Aspiration dynamics: equal abundance under vanishing selection or neutral payoffs

**Model.** $N$ individuals sit on a regular network of degree $d - 1$ and use strategy $A$ or $B$. In a $d$-player game an $A$-player facing $k$ co-players of type $A$ ($0 \le k \le d-1$) receives $a_k$, a $B$-player receives $b_k$. At each step a uniformly chosen individual $i$ plays with its $d - 1$ neighbours, obtains payoff $\pi_i$, and switches strategy with probability $g_i(\beta(e_i - \pi_i))$, where $e_i \in \mathbb{R}$ is its **personal aspiration**, $\beta \ge 0$ the selection intensity, and $g_i : \mathbb{R} \to (0, 1)$ its decision-making function. The resulting Markov chain on $\{A, B\}^N$ has no absorbing state and is ergodic, with stationary distribution $\kappa$; the average abundance of $A$ is $\langle x_A \rangle = \sum_s \kappa_s \big(\sum_i s_i\big)/N$.

**Proposition.** Assume $g_i(0) > 0$ for all $i$.

1. If $\beta = 0$, then $\langle x_A \rangle = \tfrac12$ for all aspirations $e_1, \dots, e_N$ and all decision functions.
2. If all payoff entries are equal, $a_k = b_k = h$ for all $k$, then $\langle x_A \rangle = \tfrac12$ for every $\beta \ge 0$, every choice of aspirations and every family of decision functions.

## Expansion

In both cases each individual's switching probability depends only on its own aspiration and on a payoff that does not distinguish $A$ from $B$. The global relabelling $A \leftrightarrow B$ therefore maps the transition kernel to itself, so the unique stationary distribution is invariant under it and the two strategies are equally abundant. Part 2 holds at every selection intensity, which is what makes the aspiration-independence of the weak-selection criterion possible.

## Sources

- B. Wu, L. Zhou, *Individualised aspiration dynamics: Calculation by proofs*, PLoS Comput. Biol. 14(9) (2018), e1006035 (Models section, Lemma 2). <https://doi.org/10.1371/journal.pcbi.1006035> (PMCID: PMC6177198)
