# Iterated backward difference of a multi-sequence

For a function
$a : \mathbb{N}^d \to \mathbb{R}$ and multi-indices $k, n \in \mathbb{N}^d$,

$$(\Delta^k a)_n = \sum_{j \le k} (-1)^{|k| - |j|} \binom{k}{j} \, a_{n - j},$$

where $j$ runs over the multi-indices with $j_i \le k_i$ for every $i$, $|k| = \sum_i k_i$,
$\binom{k}{j} = \prod_i \binom{k_i}{j_i}$ is the multi-index binomial coefficient, and $n - j$
is taken coordinatewise, with $n_i - j_i$ replaced by $0$ when $j_i > n_i$.

When $k \le n$ coordinatewise, $\Delta^k$ is the composite of $k_i$ applications of
$(\Delta_i a)_n = a_{n - e_i} - a_n$ in each coordinate $i$, where $e_i$ is the $i$-th unit
multi-index.
