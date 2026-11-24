# Sizes below $n$ account for every block when there are at least two

Let $n$ be a natural number and $b$ a list of natural numbers with at least two entries, each at
least $1$, whose sum is $n$. Then every entry of $b$ lies between $1$ and $n - 1$, so

$$\sum_{i=1}^{n-1} c_i(b) = \text{the number of entries of } b,$$

where $c_i(b)$ is the number of entries of $b$ equal to $i$. With a single entry the sum would
miss it, since that entry is $n$.
