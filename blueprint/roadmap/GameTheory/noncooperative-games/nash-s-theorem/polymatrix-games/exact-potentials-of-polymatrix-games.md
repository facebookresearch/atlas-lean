# Exact potentials of polymatrix games

Every symmetric polymatrix game, i.e. one with $C_{ij}(a, b) = C_{ji}(b, a)$ for all $i \ne j$, $a \in S_i$, $b \in S_j$ (on every pair the two players bear the same cost), admits the exact potential

$$
\Phi(s) = \sum_{\{i, j\}} C_{ij}(s_i, s_j),
$$

which is half the sum of all players' costs. Consequently it has the finite improvement property.

## Proof sketch

When player $i$ deviates from $s_i$ to $s'_i$, only the terms $C_{ij}(s_i, s_j)$ with $j \ne i$ change, and by symmetry their total change is exactly the change of $i$'s own cost $\sum_{j \ne i} C_{ij}(s_i, s_j)$. A finite game with an exact potential has the finite improvement property, since the potential strictly decreases along every improvement path.

## Depends on

- [Polymatrix game](polymatrix-game.md)
- [Exact potential](../../potential-games/is-exact-potential.md)

## Proof depends on

- [Generalized ordinal potentials give the finite improvement property](../../potential-games/potential-game-characterizations/generalized-ordinal-potentials-give-the-finite-improvement-property.md)

## Sources

- Elena B. Janovskaja, "Equilibrium Points in Polymatrix Games", Litovskii Matematicheskii Sbornik, 1968.
- Joseph T. Howson Jr., "Equilibria of Polymatrix Games", Management Science, 1972.
- Yang Cai and Constantinos Daskalakis, "On Minmax Theorems for Multiplayer Games", Proceedings of the 22nd Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2011), 2011, Proposition 4.1 (coordination polymatrix games, $A^{u,v} = (A^{v,u})^{\mathsf T}$, are exact potential games) and its proof, which takes half the social welfare as the potential; stated there for payoffs, whose negatives are the costs here.
- Mona Rahn and Guido Schäfer, "Efficient Equilibria in Polymatrix Coordination Games", Algorithmic Game Theory (SAGT 2015), LNCS 9347, 2015, Theorem 1, part 1 and its proof (polymatrix coordination games admit an exact potential and hence have the finite improvement property).
- Dov Monderer and Lloyd S. Shapley, "Potential Games", Games and Economic Behavior 14 (1996), 124–143, Lemma 2.3 (every finite ordinal potential game has the finite improvement property).
