# Zeckendorf digit sequence of a natural number

Let $F_k$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = F_2 = 1$). Every $n \in \mathbb{N}$ has a unique Zeckendorf representation
$n = F_{k_1} + \dots + F_{k_m}$ with $k_1 > \dots > k_m \ge 2$ and no two consecutive indices.
The Zeckendorf digit sequence of $n$ is the binary sequence $(x_k)_{k \in \mathbb{N}}$ with
$x_k = 1$ if $k$ is one of the indices $k_1, \dots, k_m$ and $x_k = 0$ otherwise.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 2.2 (the map `i`).
