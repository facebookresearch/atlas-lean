# Kasai's algorithm

Let $s$ be a list of length $n$ and $sa$ a list of natural numbers,
typically the suffix array of $s$. The algorithm visits $i = 0, 1, \dots, n - 1$ in turn, carrying
a length $k$ that starts at $0$. If $i$ occurs in $sa$, first at index $r$, with $r + 1 < |sa|$,
and $j$ is the entry of $sa$ at index $r + 1$, it records at $i$ the value $H_i = k + \ell$, where
$\ell$ is the longest-common-prefix length of the suffixes of $s$ starting at $i + k$ and at
$j + k$, found by symbol comparisons, and sets $k$ to $H_i - 1$ (truncated at $0$); otherwise it
records $H_i = 0$ and sets $k$ to $0$. It returns the list of length $|sa| - 1$ whose $t$-th entry
is $H_{sa_t}$, read as $0$ when $sa_t \ge n$. Its cost is one unit per visited position plus the
number of symbol comparisons.

## Sources

- cp-algorithms, "Suffix Array", section "Longest common prefix of two substrings without additional memory".
