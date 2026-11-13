# Parking function

Let $n \in \mathbb{N}$ and number the $n$ spots $0, \dots, n-1$.
A map $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$, giving the preferred spot of each of
$n$ cars, is a parking function if it is a partial parking function with $n$ cars and $n$
spots, that is, if for every spot $k$, at most $n - k$ cars $i$ satisfy $f(i) \ge k$.
