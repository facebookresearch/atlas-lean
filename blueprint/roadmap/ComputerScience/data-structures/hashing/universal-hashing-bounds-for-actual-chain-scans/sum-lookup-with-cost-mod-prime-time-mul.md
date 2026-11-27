# Sum lookup With Cost mod Prime time mul le of not mem

Let $p$ be prime and $m > 0$, and let $n$ be the number of distinct keys of a list of entries with keys in $\mathbb{Z}/p$. For a key absent from them, build the table from the list with the hash function of each parameter pair $(a, b)$ modulo $p$ with $a \ne 0$, and sum the scan-event count of the lookup over all $p(p - 1)$ pairs, counting a hash function once per pair that gives it. This sum, times $m$, is at most $p(p - 1)(m + n)$. The bound concerns this count of scan events, not machine time.
