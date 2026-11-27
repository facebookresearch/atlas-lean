# Privacy of AboveThreshold with discrete Laplace noise

Let the queries have sensitivity $\Delta$. If shifting the threshold noise by $\Delta$ changes its probabilities by at most a factor $e^{\varepsilon_1}$ and shifting each query noise by $2\Delta$ changes its probabilities by at most $e^{\varepsilon_2}$, then AboveThreshold is $(\varepsilon_1 + \varepsilon_2, 0)$-differentially private for any number of queries. In particular, for integer sensitivity $\Delta \ge 1$, threshold noise of discrete Laplace scale $2\Delta/\varepsilon$ and query noise of scale $4\Delta/\varepsilon$ make it $(\varepsilon, 0)$-differentially private.

## Proof sketch

Fix the query noises of the rounds before the stopping index; the output pattern $\bot^{k-1}\top$ occurs on $x$ for threshold $\hat T$ only if it occurs on the neighbour $y$ for threshold $\hat T + \Delta$ and the last query noise shifted by $2\Delta$. A change of variables in these two noises costs $e^{\varepsilon_1}$ and $e^{\varepsilon_2}$.

## Depends on

- [AboveThreshold and the sparse vector technique](above-threshold-algorithm.md)
- [The discrete Laplace (two-sided geometric) distribution](discrete-laplace-distribution.md)

## Proof depends on

- [Privacy and tails of the geometric mechanism](geometric-mechanism-privacy.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
