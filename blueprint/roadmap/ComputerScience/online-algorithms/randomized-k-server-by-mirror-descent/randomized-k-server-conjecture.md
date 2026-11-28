# The randomized k-server conjecture

The *randomized $k$-server conjecture* asserts that on every metric space with more than $k$ points there is a randomized online $k$-server algorithm that is $O(\log k)$-competitive against oblivious adversaries. On uniform metrics with more than $k$ points (paging) the optimal randomized ratio is the harmonic number $H_k = \Theta(\log k)$: $H_k$ is a lower bound, and McGeoch and Sleator gave an $H_k$-competitive algorithm. The conjecture would thus say that paging is the hardest case up to constant factors.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- Elias Koutsoupias, "The k-Server Problem", Computer Science Review 3(2) (2009).
- Amos Fiat, Richard M. Karp, Michael Luby, Lyle A. McGeoch, Daniel D. Sleator, Neal E. Young, "Competitive Paging Algorithms", Journal of Algorithms 12(4) (1991).
- Lyle A. McGeoch, Daniel D. Sleator, "A Strongly Competitive Randomized Paging Algorithm", Algorithmica 6 (1991).
