# Payoffs in groups of zero-determinant strategists

In an iterated $n$-player social dilemma, suppose every player $i = 1, \dots, n$ uses a [zero-determinant strategy](zero-determinant-strategies-in-multiplayer-social-dilemmas.md) with baseline $l_i$ and slope $s_i \ne -1/(n-1)$, and suppose not all $s_i$ equal $1$. Put

$$\kappa_i = \frac{(n-1)(1 - s_i)}{1 + (n-1)s_i} .$$

Then the long-run payoffs are

$$\pi_i = (1 + \kappa_i)\,\frac{\sum_{j=1}^n \kappa_j\, l_j}{\sum_{j=1}^n \kappa_j} - \kappa_i\, l_i, \qquad i = 1, \dots, n,$$

provided $\sum_j \kappa_j \ne 0$. In particular, the group's mean payoff is the $\kappa$-weighted mean of the baselines, $\frac1n\sum_i \pi_i = \sum_j \kappa_j l_j / \sum_j \kappa_j$. Payoffs in a group of ZD strategists therefore cost $O(n)$ operations, instead of the left eigenvector of a $2^n \times 2^n$ transition matrix needed for general memory-one strategies.

## Depends on

- [Zero-determinant strategies in multiplayer social dilemmas](zero-determinant-strategies-in-multiplayer-social-dilemmas.md)

## Proof sketch

Let $\Sigma = \sum_j \pi_j$. Player $i$'s enforced relation $\frac{\Sigma - \pi_i}{n-1} = s_i\pi_i + (1 - s_i)l_i$ gives $\pi_i\,(1 + (n-1)s_i) = \Sigma - (n-1)(1 - s_i)\,l_i$. Since $1 + \kappa_i = n/(1 + (n-1)s_i)$, this is $\pi_i = (1 + \kappa_i)\,\Sigma/n - \kappa_i l_i$. Summing over $i$ gives $\Sigma = \Sigma + \Sigma\sum_j\kappa_j/n - \sum_j \kappa_j l_j$, i.e. $\Sigma/n = \sum_j\kappa_j l_j/\sum_j\kappa_j$, and substituting back yields the formula (Eqs. (3)–(4) and Appendix A.2 of the source). If all $s_i = 1$ every relation reads $\pi_{-i} = \pi_i$, so all payoffs are equal but not determined by the strategies' parameters alone.

## Sources

- C. Hilbe, B. Wu, A. Traulsen, M. A. Nowak, "Evolutionary performance of zero-determinant strategies in multiplayer games", Journal of Theoretical Biology (2015), <https://doi.org/10.1016/j.jtbi.2015.03.032> (PMC4425415).
