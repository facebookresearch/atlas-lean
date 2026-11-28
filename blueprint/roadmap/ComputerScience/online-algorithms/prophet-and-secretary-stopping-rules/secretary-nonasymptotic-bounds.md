# Non-asymptotic 1/e bounds for the secretary problem

In the secretary problem with $n \ge 1$ candidates in uniformly random order, where the employer sees only relative ranks and wins by hiring the overall best, let

$$
p_n^* = \max_{1 \le r \le n} \frac{1}{n} \sum_{k = r}^{n} \frac{r - 1}{k - 1},
$$

where the summand $(r-1)/(k-1)$ is read as $1$ when $r = k = 1$; this is the win probability of the best rule that rejects the first $r - 1$ candidates and then hires the first candidate better than all previous ones. Then:

1. the relative ranks of a uniform random permutation are independent, the $i$-th uniform on $\{0, \dots, i-1\}$;
2. no rank-based rule wins with probability more than $p_n^*$;
3. the cutoff rule that rejects the first $\lfloor n/e \rfloor$ candidates and then hires the first candidate better than all previous ones wins with probability at least $1/e - 1/n$;
4. $p_n^*$ is non-increasing in $n$ and at least $1/e$ for every $n \ge 1$.

## Proof sketch

Independence of relative ranks follows from the bijection between permutations and rank sequences. Among rank-based rules an optimal one may be taken to be a cutoff rule, since stopping on a relatively best candidate at stage $j$ wins with probability $j/n$, which increases in $j$, while the best win probability after passing $j$ candidates does not; the cutoff-$r$ win probability is the expression inside the maximum. Comparing $\sum_k \frac{1}{k-1}$ with $\int dx/x$ gives $1/e - 1/n$ at $r = \lfloor n/e\rfloor + 1$, and also the upper bound $p_n^* \le 1/e + 1/n$, since $\frac{r-1}{n}\sum_{k=r}^{n}\frac{1}{k-1} \le \frac1n + \frac{r-1}{n}\ln\frac{n}{r-1} \le \frac1n + \frac1e$.

## Depends on

- [Win probability of a threshold rule in the secretary problem](../../../Probability/martingales/secretary-problem/win-prob.md)
- [Optimal threshold of the secretary problem](../../../Probability/martingales/secretary-problem/optimal-threshold.md)

## Proof depends on

- [Optimality of the threshold rule among all rank-based rules](../../../Probability/martingales/secretary-problem/card-rank-rule-wins-div-factorial-le.md)
- [The $1/e$ law of the secretary problem](../../../Probability/martingales/secretary-problem/tendsto-win-prob-optimal-threshold.md)

## Sources

- Dennis V. Lindley, "Dynamic Programming and Decision Theory", Journal of the Royal Statistical Society, Series C 10, 1961.
- Thomas S. Ferguson, "Who Solved the Secretary Problem?", Statistical Science 4(3), 1989.
- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007.
- T. S. Ferguson, "Optimal Stopping and Applications", Ch. 2 "Finite Horizon Problems", §2.1 "The Classical Secretary Problem", UCLA: independence and uniformity of the relative ranks, the reduction to threshold rules $N_r$ and their win probability (3), and the optimal threshold (4). <https://www.math.ucla.edu/~tom/Stopping/sr2.pdf>
- T. Kesselheim, "Algorithms and Uncertainty", University of Bonn, Winter 2025/26, Lecture 10 "Optimal Stopping: Secretary Problem": Theorem 10.1 with the bound at $\tau = \lfloor n/e \rfloor$, and Theorem 10.3. <https://thomas-kesselheim.de/lecturenotes/aau/lecturenotes10.pdf>
- K. Siegrist, "Random: Probability, Mathematical Statistics, Stochastic Processes", §11.9 "The Secretary Problem": monotonicity of the optimal success probability and its limit $1/e$. <https://www.randomservices.org/random/urn/Secretary.html>
