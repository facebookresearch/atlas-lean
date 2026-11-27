# Non-asymptotic 1/e bounds for the secretary problem

In the secretary problem with $n \ge 1$ candidates in uniformly random order, where the employer sees only relative ranks and wins by hiring the overall best:

1. the relative ranks of a uniform random permutation are independent, the $i$-th uniform on $\{0, \dots, i-1\}$;
2. no rank-based rule wins with probability more than $1/e + 1/n$;
3. the cutoff rule that rejects the first $\lfloor n/e \rfloor$ candidates and then hires the first candidate better than all previous ones wins with probability at least $1/e - 1/n$;
4. the success probability of the optimal cutoff rule is non-increasing in $n$ and at least $1/e$ for every $n \ge 1$.

## Proof sketch

Independence of relative ranks follows from the bijection between permutations and rank sequences. The cutoff-$r$ success probability $\frac{r-1}{n}\sum_{k=r}^n \frac1{k-1}$ is compared with $\int dx/x$ to give the two-sided $1/n$ bounds at $r = \lfloor n/e\rfloor + 1$, and optimality of the best cutoff among all rank-based rules transfers the upper bound to every rule.

## Depends on

- [Win probability of a threshold rule in the secretary problem](../../../Probability/martingales/secretary-problem/win-prob.md)
- [Optimal threshold of the secretary problem](../../../Probability/martingales/secretary-problem/optimal-threshold.md)

## Proof depends on

- [Optimality of the threshold rule among all rank-based rules](../../../Probability/martingales/secretary-problem/card-rank-rule-wins-div-factorial-le.md)
- [Win probability of a threshold rule in the secretary problem](../../../Probability/martingales/secretary-problem/win-prob.md)
- [The $1/e$ law of the secretary problem](../../../Probability/martingales/secretary-problem/tendsto-win-prob-optimal-threshold.md)

## Sources

- Dennis V. Lindley, "Dynamic Programming and Decision Theory", Journal of the Royal Statistical Society, Series C 10, 1961.
- Thomas S. Ferguson, "Who Solved the Secretary Problem?", Statistical Science 4(3), 1989.
- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007.
