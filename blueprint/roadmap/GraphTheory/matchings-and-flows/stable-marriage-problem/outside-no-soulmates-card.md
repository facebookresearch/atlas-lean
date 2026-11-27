# Outsiders without soulmate pairs

Let $n$ and $k$ be natural numbers, where $n - k$ is
read as $0$ when $k > n$. Consider the $n - k$ men $k, \dots, n - 1$ and the $n - k$ women
$k, \dots, n - 1$ among $n$ men and $n$ women numbered from $0$, where each of these men ranks all
$n$ women and each of these women ranks all $n$ men. The number of ways to choose these rankings
so that no man and woman among them each rank the other first is

$$\sum_{i=0}^{n-k} (-1)^i \binom{n-k}{i}^2 ((n-1)!)^{2i}\, i!\, (n!)^{2(n-k-i)}.$$

This number is the paper's $S(k, n)$: the preferences of the remaining $k$ men and $k$ women are
ignored.

## Sources

- Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer Sequences 27 (2024), Article 24.2.2, Lemma 4 (`jis-2024-24.2.2-lem-4`).
