# Exact potential of a finite game

Let finitely many players $i$ have finite nonempty strategy sets $S_i$ and costs
$c_i : \prod_j S_j \to \mathbb{R}$. A function $\Phi$ on strategy profiles is an exact potential when
every unilateral deviation changes the deviating player's cost by exactly the change in $\Phi$:

$$c_i(a, s_{-i}) - c_i(s) = \Phi(a, s_{-i}) - \Phi(s)$$

for every player $i$, profile $s$ and strategy $a \in S_i$, where $(a, s_{-i})$ is $s$ with its $i$-th
coordinate replaced by $a$. The definition is that of [exact potential](is-exact-potential.md),
restricted to finitely many players with finite nonempty strategy sets.
