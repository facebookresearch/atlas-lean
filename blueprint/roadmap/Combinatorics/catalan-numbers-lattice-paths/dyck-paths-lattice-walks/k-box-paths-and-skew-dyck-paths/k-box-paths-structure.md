# Structure of $k$-box paths

Let $k \ge 1$ and $n \ge 1$. For a list
$a = (a_1, \dots, a_n)$ of natural numbers write
$w_k(a) = U^{a_1} D^k L D \cdots U^{a_{n-1}} D^k L D\, U^{a_n} D^k L$. Every $k$-box path of
size $n$ equals $w_k(a)$ for some list $a$ of $n$ positive integers. Conversely, if $a$ is a
list of $n$ positive integers with $a_1 + \cdots + a_n = (k+2)n - 1$ and no prefix of $w_k(a)$
has more $D$s and $L$s together than $U$s, then $w_k(a)$ is a $k$-box path of size $n$.

## Sources

- Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2 (`jis-2024-24.2.4-lem-2`).
