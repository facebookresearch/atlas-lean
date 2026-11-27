# Suffix count of a stream position

For a stream $l = (a_0, \dots, a_{m-1})$ over a set with decidable equality and a position $p < m$, the suffix count of $p$ is

$$r = \#\{q : p \le q < m,\ a_q = a_p\},$$

the number of occurrences of $a_p$ from position $p$ on, including $p$ itself; in particular $r \ge 1$ (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.1).
