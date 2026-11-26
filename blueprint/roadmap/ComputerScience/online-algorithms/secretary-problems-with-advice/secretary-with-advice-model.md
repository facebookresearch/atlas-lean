# Secretary problems with advice

In a *secretary problem with advice*, $n$ candidates with distinct qualities arrive in uniformly random order; upon each arrival the algorithm observes the candidate's relative rank among those seen so far together with an *advice signal* drawn from a known joint distribution with the ranks (for example: samples of other candidates seen in advance, the quality drawn from a known distribution, or a noisy binary classifier output indicating whether the candidate is the overall best). The algorithm must accept or reject each candidate irrevocably and wins if it accepts the overall best candidate; the goal is to maximize the win probability.

## Sources

- Paul Dütting, Silvio Lattanzi, Renato Paes Leme, Sergei Vassilvitskii, "Secretaries with Advice", EC (2021); Mathematics of Operations Research 49(2) (2024), arXiv:2011.06726.
