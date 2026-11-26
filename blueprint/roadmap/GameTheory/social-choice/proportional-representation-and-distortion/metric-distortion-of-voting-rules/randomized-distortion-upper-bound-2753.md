# A randomized voting rule with metric distortion below 2.753

There is a randomized voting rule with metric distortion at most $2.753$; hence randomization strictly improves on the optimal deterministic distortion $3$. The rule mixes Maximal Lotteries, the distribution that is a Nash equilibrium of the symmetric zero-sum game given by pairwise majority margins, with a hybrid of Random Dictatorship and Copeland-type rules.

## Proof sketch

Neither component alone beats distortion $3$, but their bad instances are complementary: Maximal Lotteries performs well when the optimum wins many pairwise contests, while dictatorship-based hybrids perform well when the profile is fragmented. Formulating the worst-case ratio of a mixture as an optimization over a compact family of "biased metrics" allows numerical certification of the bound below $2.753$.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)
- [Maximal lotteries](maximal-lotteries.md)

## Proof depends on

- [Random dictatorship has metric distortion 3 - 2/n](random-dictatorship-distortion.md)
- [Metric distortion of plurality, Borda and Copeland](plurality-borda-copeland-distortion.md)

## Sources

- M. Charikar, P. Ramakrishnan, K. Wang, H. Wu, "Breaking the Metric Voting Distortion Barrier", SODA 2024, arXiv:2306.17838.
