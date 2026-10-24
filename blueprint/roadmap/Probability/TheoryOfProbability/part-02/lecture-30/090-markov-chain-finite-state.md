---
article_id: af_9fabb7f0780103be7abfb973
declaration: structure
origin: cited
statement: formalized
lean: IsFiniteMarkovChain
---

# Definition (Markov chain, finite state)

Consider a sequence of random variables $X_0, X_1, X_2, \ldots$ each taking values in a finite set $\{0, 1, \ldots, M\}$. The sequence is called a Markov chain if we have a fixed collection of numbers $P_{ij}$ such that $P\{X_{n+1} = j \mid X_n = i, X_{n-1} = i_{n-1}, \ldots, X_1 = i_1, X_0 = i_0\} = P_{ij}$.

## Depends on

- [Definition (Filtration)](../../part-01/lecture-25/063-filtration.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 30/31, Markov chains section](../../../../../sources/v1/TheoryOfProbability.md)
