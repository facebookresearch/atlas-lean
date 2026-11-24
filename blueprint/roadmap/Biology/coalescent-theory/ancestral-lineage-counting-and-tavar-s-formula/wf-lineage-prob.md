# Wright–Fisher transition probability of the lineage count

For natural numbers $M$, $k$ and $j$, let

$$p_M(k, j) = \frac{S(k, j)\, M(M-1)\cdots(M-j+1)}{M^{k}},$$

where $S(k, j)$ is the Stirling number of the second kind and the numerator contains the falling factorial of $M$ of length $j$, with the convention that division by $0$ gives $0$ (so for $M = 0$ and $k \ge 1$ the value is $0$). For $M \ge 1$, this is the probability that $k$ gene copies of a neutral Wright–Fisher population of $M$ gene copies, each choosing its parent uniformly and independently among the $M$ copies of the previous generation, have exactly $j$ distinct parents.
