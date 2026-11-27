# Pure Nash equilibria of explicit congestion games are in PLS

Encode an atomic congestion game by listing each player's strategies as resource sets and each resource's cost table $c_e(1), c_e(2), \dots$. Finding a pure Nash equilibrium of such an encoded game is a polynomial local search problem: profiles are encoded as bit strings, Rosenthal's potential is computable in polynomial time, every profile that is not an equilibrium has a neighbour (an improving unilateral move) of strictly smaller potential computable in polynomial time, and local optima are exactly the pure Nash equilibria.

## Proof sketch

The local-search instance takes the potential as cost and the best improving move as neighbourhood function; both are evaluable by scanning the explicit tables.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)
- [Explicit encoding and size of finite games](../../explicit-encoding-and-size-of-finite-games.md)

## Proof depends on

- [Rosenthal's theorem](../../potential-games/is-exact-potential-potential.md)
- [Pure equilibria of potential games as local search](../../potential-games/pure-equilibria-of-potential-games-as-local-search.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
- Alex Fabrikant, Christos H. Papadimitriou and Kunal Talwar, "The Complexity of Pure Nash Equilibria", Proceedings of the 36th Annual ACM Symposium on Theory of Computing, 2004.
- David S. Johnson, Christos H. Papadimitriou and Mihalis Yannakakis, "How Easy Is Local Search?", Journal of Computer and System Sciences, 1988.
