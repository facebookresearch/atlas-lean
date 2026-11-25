# Parity of the smallest index in a non-commuting list

Let $a$ be a binary keyword of
length $m + 1$, let $n$ and $i$ be natural numbers with $i < n$, and for each index $k$ let
$\varphi_k$ be the simple map of $a$ at letter $k$ on binary words of length $n$. Let
$l = [j_1, \dots, j_r]$ be a list of indices that are all greater than $i$, and let
$\varphi_l = \varphi_{j_r} \circ \dots \circ \varphi_{j_1}$ be the map that applies
$\varphi_{j_1}$ first. Suppose that $\varphi_i \circ \varphi_l \ne \varphi_l \circ \varphi_i$
as maps on words of length $n$, and that the list $[i, j_1, \dots, j_r, i]$, applied from left
to right, acts completely on some word of length $n$ (each map in turn changes the word). Then
every entry $j$ of $l$ with $j \le j'$ for all entries $j'$ of $l$ occurs an even number of
times in $l$.

## Sources

- Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood, *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 8 (`jis-2025-25.6.6-lem-8`).
