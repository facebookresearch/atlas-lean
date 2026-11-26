# Bounded overlap search

For lists $a$ and $b$ and a natural number $n$, the greatest $k \le n$ that is a [matching overlap length](overlap-match.md) of $a$ and $b$ (the suffix of $a$ of length $k$ equals the prefix of $b$ of length $k$, with $k \le \min(|a|, |b|)$), found by trying $k = n, n - 1, \dots, 1$; it is $0$ when no positive $k \le n$ matches.
