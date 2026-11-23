# Hypergeometric mass function

For $N, K, n, k \in \mathbb{N}$, the hypergeometric mass function is

$$h(N, K, n, k) = \begin{cases} \dfrac{\binom{K}{k} \binom{N - K}{n - k}}{\binom{N}{n}} & \text{if } k \le n, \\ 0 & \text{if } k > n, \end{cases}$$

where $N - K$ is truncated subtraction ($0$ if $K > N$) and a quotient with zero denominator is
read as $0$. For $K \le N$ and $n \le N$ it is the probability of drawing exactly $k$ marked items
in $n$ draws without replacement from $N$ items of which $K$ are marked; outside that range it is
not a probability (for $n > N$, $\binom{N}{n} = 0$ makes it $0$).
