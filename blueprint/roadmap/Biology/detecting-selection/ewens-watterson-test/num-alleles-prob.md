# Probability of a given number of alleles under the Ewens formula

For a real $\theta$ and natural numbers $n, k$, put

$$P_\theta(K = k) = \sum_{\pi \,:\, K(\pi) = k} P_\theta(\pi),$$

the sum over the partitions $\pi$ of $n$ with $K(\pi) = k$ parts (alleles), where $P_\theta(\pi) = \frac{n!}{\theta^{(n)}} \prod_j \frac{\theta^{a_j}}{j^{a_j} a_j!}$ is the Ewens sampling formula, $\theta^{(n)} = \theta(\theta + 1) \cdots (\theta + n - 1)$ the rising factorial and $x/0 = 0$. For $\theta > 0$ it is the probability that a sample of $n$ genes carries $k$ distinct alleles.
