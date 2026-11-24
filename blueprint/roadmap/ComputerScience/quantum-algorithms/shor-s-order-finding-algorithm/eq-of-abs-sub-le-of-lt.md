# Uniqueness of the fraction recovered in Shor's algorithm

Let $\xi$ be a real number and let $q$ and $n$ be natural numbers with $n^2 \le q$. If two
fractions $d/r$ and $d'/r'$ with integer numerators and natural denominators $0 < r < n$ and
$0 < r' < n$ both satisfy $|\xi - d/r| \le 1/(2q)$ and $|\xi - d'/r'| \le 1/(2q)$, then
$d/r = d'/r'$.

In Shor's algorithm $\xi = c/q$, where $c$ is the observed output, and the inequality
$|c/q - d/r| \le 1/(2q)$ is equation (5.13). The statement is Shor's remark that, because
$q > n^2$, at most one fraction $d/r$ with $r < n$ satisfies it; the proof needs only
$q \ge n^2$. Two distinct such fractions would differ by at least $1/(rr') > 1/n^2 \ge 1/q$,
while both lie within $1/(2q)$ of $\xi$.

The hypothesis $n^2 \le q$ cannot be dropped: with $q = n = 16$, both $1/3$ and $4/11$ lie
within $1/32$ of $0.35$.

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509, arXiv:quant-ph/9508027, Section 5, equations (5.12)–(5.13) and the paragraph after them.
