# Humps and peaks at a given height in Motzkin paths

Let $n \ge 2$ and $k \ge 1$. A Motzkin
path of length $n$ is a sequence of $n$ steps, each up ($+1$), flat ($0$) or down ($-1$), whose
partial sums are all nonnegative and whose total is $0$. A hump at height $k$ of such a path is
a pair of positions $i < j$ such that step $i$ is up, step $j$ is down, every step strictly
between them is flat, and the sum of the steps up to and including step $i$ equals $k$; a peak
at height $k$ is such a hump with $j = i + 1$. Let $H_{n,k}$ be the number of pairs consisting
of a Motzkin path of length $n$ and a hump at height $k$ of it, and let $P_{n,k}$ be the same
count for peaks. Then, as rational numbers,

$$H_{n,k} = \sum_{j} \frac{4k}{n - j + 2k} \binom{n}{j} \binom{n - j - 1}{(n - j)/2 + k - 1}$$

and

$$P_{n,k} = \sum_{j} \frac{4k}{n - j + 2k} \binom{n - 1}{j} \binom{n - j - 1}{(n - j)/2 + k - 1},$$

where both sums run over the integers $0 \le j \le n - 2k$ with $j \equiv n \pmod 2$.

## Sources

- Xiaomei Chen, "Humps in Motzkin Paths and Standard Young Tableaux in a $(2,1)$-Hook", Journal of Integer Sequences 28 (2025), Article 25.8.1, Theorem `thm:22`, lines 147-156, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Chen/chen36.tex>.
