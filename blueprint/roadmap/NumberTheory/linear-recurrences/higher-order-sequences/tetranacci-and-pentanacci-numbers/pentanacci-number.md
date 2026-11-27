# Pentanacci numbers

The pentanacci numbers $a_n$, for natural numbers $n$, are defined by
$a_0 = 1$, $a_1 = 1$, $a_2 = 2$, $a_3 = 4$, $a_4 = 8$ and
$a_{n+5} = a_{n+4} + a_{n+3} + a_{n+2} + a_{n+1} + a_n$ for every $n$, so each term from index
$5$ on is the sum of the five terms before it.

Their ordinary generating function is $1/(1 - t - t^2 - t^3 - t^4 - t^5)$; up to a shift of index
they form OEIS A001591.
