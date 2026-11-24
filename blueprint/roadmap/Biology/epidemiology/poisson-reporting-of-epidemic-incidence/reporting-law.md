# Independent Poisson reporting law of interval counts

For a number $n$ of intervals, the reporting law is the Markov kernel from intensity vectors
$\lambda \in [0, \infty)^n$ to count vectors $k \in \mathbb{N}^n$ that sends $\lambda$ to the
product of [Poisson laws](../../../Probability/distributions/discrete/poisson-distribution/README.md)

$$\bigotimes_{j=0}^{n-1} \operatorname{Po}(\lambda_j):$$

the reported counts of the $n$ intervals are independent and the count of interval $j$ is Poisson
with mean $\lambda_j$. An interval with intensity $0$ reports $0$ almost surely, the Poisson law
with mean $0$ being the point mass at $0$. For $n = 0$ the law is the point mass at the empty count
vector. Independence of the counts and Poisson dispersion are modelling assumptions about reporting.
