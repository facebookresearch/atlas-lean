# Weighted Chernoff tail for machine loads

Let $p$ be a mixed profile of a load-balancing game on identical machines and let $W$ bound all job weights. For every machine $j$ and $\delta > 0$, the probability that the load of $j$ is at least $(1 + \delta)\, \mathbb{E}[\ell_j]$ is at most $\bigl(e^{\delta} / (1+\delta)^{1+\delta}\bigr)^{\mathbb{E}[\ell_j] / W}$, by the Chernoff bound for independent $[0, 1]$-valued normalized contributions $w_i \mathbf 1[A(i) = j] / W$.

## Proof sketch

Apply the multiplicative Chernoff bound to the independent bounded variables obtained by normalizing each job's contribution by the maximum weight.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)
- [Chernoff bound for the empirical mean of real-valued i.i.d. variables](../../../../Probability/large-deviations/cram-r-s-theorem/measure-empirical-mean-le-of-threshold.md)

## Sources

- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
- Michael Mitzenmacher and Eli Upfal, "Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis", Cambridge University Press, 2017.
