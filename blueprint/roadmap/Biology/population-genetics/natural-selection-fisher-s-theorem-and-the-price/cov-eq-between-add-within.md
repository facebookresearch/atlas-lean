# Law of total covariance for a nested finite population

Let a finite population be divided into finitely many groups $k$, group $k$ having a finite set of
$n_k$ members $j$, and let $N = \sum_k n_k$ be the population size. For real traits $x$ and $y$ of
the individuals $(k, j)$, let $q_k = n_k / N$ be the weight of group $k$, proportional to its size,
and let $X_k$ and $Y_k$ be the averages of $x$ and $y$ over the members of group $k$. Then the
population covariance of $x$ and $y$, with every individual weighted equally (divisor $N$), splits
into the size-weighted covariance of the group means (between groups) and the size-weighted mean of
the within-group population covariances:

$$
\mathbb{E}\bigl[(x - \bar x)(y - \bar y)\bigr] =
\sum_k q_k \Bigl(X_k - \sum_l q_l X_l\Bigr)\Bigl(Y_k - \sum_l q_l Y_l\Bigr) +
\sum_k q_k\, \mathbb{E}_j\bigl[(x_{kj} - X_k)(y_{kj} - Y_k)\bigr],
$$

where $\mathbb{E}$ averages over the whole population, $\bar x = \mathbb{E}[x]$ and
$\bar y = \mathbb{E}[y]$, and $\mathbb{E}_j$ averages over the members of group $k$. No hypothesis
is needed: an average over an empty set is $0$, an empty group has weight $0$, and for an empty
population ($N = 0$) the convention $a / 0 = 0$ makes every weight $0$, so that both sides are $0$.
