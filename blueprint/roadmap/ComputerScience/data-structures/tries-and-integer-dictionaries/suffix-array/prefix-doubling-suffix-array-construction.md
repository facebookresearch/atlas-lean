# Suffix-array construction by prefix doubling

Let $T = t_0 t_1 \cdots t_{n-1}$ be a string of length $n \ge 1$ over the alphabet
$\{0, 1, \dots, n\}$ whose last symbol $t_{n-1}$ is smaller than each of its other symbols. Then
the [suffix array](suffix-array.md) of $T$ can be computed in $O(n \log n)$ time on a
[word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
by prefix doubling, which sorts the cyclic substrings of $T$ of lengths
$1, 2, 4, \dots, 2^{\lceil \log_2 n \rceil}$ in $\lceil \log_2 n \rceil + 1$ rounds of $O(n)$
time each.

## Proof sketch

Take indices modulo $n$. Round $0$ sorts the symbols of $T$ with one counting sort and gives each
position $i$ the class $c_0(i)$ of $t_i$: the number of distinct symbols of $T$ smaller than
$t_i$. After round $k$, the positions are sorted by their cyclic substrings
$t_i t_{i+1} \cdots t_{i + 2^k - 1}$ of length $2^k$, and $c_k(i) < n$ is the number of distinct
such substrings smaller than the one at $i$. The substring of length $2^{k+1}$ at $i$ is the pair
of the substrings of length $2^k$ at $i$ and at $i + 2^k$, so it is ordered by the pair
$(c_k(i), c_k(i + 2^k))$. Shifting each position of the order of round $k$ back by $2^k$ orders the
positions by the second component; one stable counting sort by the first component then gives the
order of round $k + 1$, and one scan over it gives $c_{k+1}$. After round $\lceil \log_2 n \rceil$
the cyclic shifts of $T$ are sorted, since $2^{\lceil \log_2 n \rceil} \ge n$. As $t_{n-1}$ occurs
only at the end of $T$ and is smaller than every other symbol, the order of the cyclic shifts is
the order of the suffixes, so the final order is the suffix array.

## Depends on

- [Suffix array](suffix-array.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Running time of counting sort](../../../sorting-and-searching/counting-sort/counting-sort-time.md)

## Sources

- cp-algorithms, "Suffix array", <https://cp-algorithms.com/string/suffix-array.html>: section
  "$O(n \log n)$ approach", with the $\lceil \log n \rceil + 1$ rounds sorting the cyclic
  substrings of length $2^k$, the order by the second component obtained by shifting the previous
  order, one counting sort by the first component per round, and the reduction from suffixes to
  cyclic shifts by appending a symbol smaller than all others.
