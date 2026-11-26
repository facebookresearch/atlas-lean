# Squared-logarithmic randomized k-server bound

There is a universal real $C>0$ such that for every $k\ge2$, every metric space with at least $k+1$ distinct points, and every initial placement of $k$ labelled servers, there is one policy and $B\ge0$ such that $B=0$ if the placement is injective and every fixed finite request list $w$ satisfies

$$
\mathbb E\operatorname{cost}(w)\le C(\log(k+1))^2\operatorname{OPT}(w)+B.
$$

The policy assigns a probability distribution on server labels to the history of request–label pairs and the current request. It moves just the selected server to that request and pays the old-to-new distance. The expected cost sums over finite label sequences with weights given by the product of the successive probabilities. The offline optimum is the infimum of costs over all such label sequences from the same initial placement.

## Depends on

- [The k-server model](the-k-server-problem.md)
- History-dependent distributions, their finite product law, and the labelled offline optimum.

## Proof outline

State the finite-path cost and competitive analysis for the same policy across all horizons. Handle repeated starting positions separately and check that the comparator uses no diameter, finiteness, or adaptive-adversary premise.

- Uniform competitive bound for the random policy and zero additive loss for distinct initial positions.

## Sources

- [Comparator statement: `OAI.KServer.main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KServer.lean#L62-L64)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/110.md)
