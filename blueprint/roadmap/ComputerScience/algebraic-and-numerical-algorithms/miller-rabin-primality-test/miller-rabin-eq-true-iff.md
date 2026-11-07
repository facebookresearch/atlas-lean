# Miller–Rabin answers prime exactly when no base is a witness

For every natural number
$n$ and every list of bases, the Miller–Rabin test on $n$ with these bases answers *prime* if and
only if, for every base $a$ in the list, the witness test $\mathrm{WITNESS}(a, n)$ returns false,
that is, $a$ is not a witness to the compositeness of $n$.
