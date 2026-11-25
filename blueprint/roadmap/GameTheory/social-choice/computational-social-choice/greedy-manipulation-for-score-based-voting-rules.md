# Greedy manipulation for score-based voting rules

Consider a voting rule given by a score function $S(P, i)$ of a preference profile $P$ and candidate $i$,
computable in polynomial time, where the winner is a candidate of best score, and which is monotone: whenever,
in a profile $P'$, candidate $i$ is ranked above a subset of the candidates it is ranked above in $P$, the score
of $i$ in $P'$ is no better than in $P$. Then the following greedy algorithm decides in polynomial time whether
a single manipulator can make a given candidate $c$ win, and constructs such a vote when one exists: place $c$
first, then repeatedly place next any remaining candidate whose placement in that slot does not make it beat
$c$, and fail if no remaining candidate can be placed.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Standard voting rules.

## Sources

- J. J. Bartholdi III, C. A. Tovey and M. A. Trick, *The computational difficulty of manipulating an election*, Soc. Choice Welf. 6 (1989) 227–241, Theorem 1, its corollary and the Greedy-Manipulation algorithm. <http://www.cs.cmu.edu/~arielpro/15896s15/docs/BTT89.pdf>
