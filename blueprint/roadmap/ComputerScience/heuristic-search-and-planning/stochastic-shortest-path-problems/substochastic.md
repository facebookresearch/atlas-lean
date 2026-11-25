# Substochastic transitions

A Markov decision process with real transition probabilities $p(s, a, s')$ among its nonterminal states is substochastic if $p(s, a, s') \ge 0$ for all $s, a, s'$ and $\sum_{s'} p(s, a, s') \le 1$ for all $s, a$. The missing mass $1 - \sum_{s'} p(s, a, s')$ is the probability of moving from $s$ under action $a$ to the termination state, which is cost-free and absorbing and is not modelled explicitly.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Example 1.2.6 (the matrix of transition probabilities among the nonterminal states is substochastic).
