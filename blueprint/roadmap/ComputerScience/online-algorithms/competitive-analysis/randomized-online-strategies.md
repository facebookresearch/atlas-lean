# Randomized online strategies against an oblivious adversary

Against an *oblivious adversary*, which fixes the entire request sequence before any coin is tossed, a randomized online strategy can be modelled in two ways.

- A *mixed strategy* is a probability distribution over deterministic online strategies, drawn before the first request.
- A *behavioural strategy* has internal memory and, at each request, draws its next memory (and hence its next configuration) from a distribution depending on the current memory and request.

Its expected cost on $\sigma$ is defined by backward recursion over the requests, and it is *$(c, b)$-competitive* if its expected cost is at most $c \cdot \mathrm{OPT}(s_0, \sigma) + b$ for every admissible $s_0$ and $\sigma$. A deterministic strategy is the special case of point-mass transitions, and its expected cost equals its cost.

## Depends on

- [Online request-serving problem and competitive ratio](online-problem-and-competitive-ratio.md)
- [Las Vegas and Monte Carlo algorithms](../../randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)

## Sources

- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
- A. Fiat, R. M. Karp, M. Luby, L. A. McGeoch, D. D. Sleator and N. E. Young, "Competitive Paging Algorithms", Journal of Algorithms 12(4), 1991; arXiv:cs/0205038.
