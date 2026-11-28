# Secretary problems with advice

In a *secretary problem with advice*, $n$ candidates with distinct ranks arrive one at a time, and each candidate is paired with an *advice signal* from a signal space; the ranks of the candidates in arrival order and their signals are drawn from a known joint distribution (the classical uniformly random arrival order is a special case). Upon each arrival the algorithm observes the relative order of the candidates seen so far together with their signals. Examples are samples of other candidates seen in advance, the quality drawn from a known distribution (the full-information problem), and a noisy binary classifier output indicating whether the candidate is the overall best. Upon each arrival the algorithm must irrevocably either accept (hire) the current candidate, which ends the game, or reject it and continue, so at most one candidate is hired. It wins if the hired candidate is the overall best; hiring no one loses. The goal is to maximize the win probability.

## Sources

- Paul Dütting, Silvio Lattanzi, Renato Paes Leme, Sergei Vassilvitskii, "Secretaries with Advice", EC (2021); Mathematics of Operations Research 49(2) (2024), arXiv:2011.06726, Section 1 and Section 2.
