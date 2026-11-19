# Pure Nash equilibrium

Consider a strategic game with players $i \in I$, strategy sets $S_i$ and costs
$c_i : \prod_j S_j \to \mathbb R$, which each player wants to minimise. A strategy profile $s$ is a
pure Nash equilibrium if no player can lower its cost by changing only its own strategy:
$c_i(s) \le c_i(a, s_{-i})$ for every player $i$ and every $a \in S_i$, where $(a, s_{-i})$ is
$s$ with the $i$-th coordinate replaced by $a$.

## Sources

- D. Monderer and L. S. Shapley, "Potential games", Games Econom. Behav. 14 (1996), 124–143, §2.
