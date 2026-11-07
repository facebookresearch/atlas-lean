# Prefix value of a digit sequence

For $k \in \mathbb{N}$ and a binary sequence
$x = (x_i)_{i \in \mathbb{N}}$, the prefix value of order $k$ is the natural number
$v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, where $F_i$ is the $i$-th Fibonacci number
($F_1 = F_2 = 1$). It is the value of the block $x_{k+1} \cdots x_2$ of the $k$ rightmost digits
of $x$, the name of the cylinder of order $k$ that contains $x$.

In the paper the levels of the two Rokhlin towers of order $k$ are level sets of $v_k$: the
large tower has levels $\{v_k = j - 1\}$ for $1 \le j \le F_{k+1}$, and the small tower has
levels $\{v_k = F_{k+1} + j - 1\}$ for $1 \le j \le F_k$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 3.1 (cylinders of order `k` and the two towers).
