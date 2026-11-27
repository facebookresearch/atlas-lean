# Querying a vector of points

The oracle computation that queries the points $p_0, \dots, p_{n-1}$ in order and returns the vector of answers: for $n = 0$ it returns the empty vector, and for $n + 1$ it queries $p_0$, then queries the remaining points $p_1, \dots, p_n$ in the same way, and returns the first answer followed by the others. It is generic in the query and answer types; the random-oracle version is its instance at the oracle's domain and range.
