# Cross moment of two polygenic scores

Let $\nu$ be a measure on a measurable space $\Xi$ and let $x_1, \dots, x_M$ be real functions on $\Xi$ that are square integrable with respect to $\nu$ and satisfy

$$\int x_j x_k \, d\nu = \begin{cases} 1 & j = k,\\ 0 & j \ne k. \end{cases}$$

Then for all $a, b \in \mathbb{R}^M$,

$$\int \Bigl(\sum_{j=1}^{M} a_j x_j\Bigr)\Bigl(\sum_{k=1}^{M} b_k x_k\Bigr) d\nu = \sum_{j=1}^{M} a_j b_j.$$

When $\nu$ is a probability measure on a target population and the marker genotypes $x_j$ have mean zero (standardized, uncorrelated markers), this says that the covariance of the genetic value $x^\top \beta$ and the polygenic score $x^\top \hat\beta$ is $\beta^\top \hat\beta$.
