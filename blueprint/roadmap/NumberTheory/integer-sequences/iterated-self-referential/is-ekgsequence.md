# The EKG sequence

A sequence $a_0, a_1, a_2, \dots$ of natural numbers is an EKG
sequence when $a_0 = 1$, $a_1 = 2$, and for every $n \ge 0$ the term $a_{n+2}$ is positive,
differs from each of $a_0, \dots, a_{n+1}$, satisfies $\gcd(a_{n+1}, a_{n+2}) > 1$, and
satisfies $a_{n+2} \le m$ for every positive integer $m$ that differs from each of
$a_0, \dots, a_{n+1}$ and has $\gcd(a_{n+1}, m) > 1$. Thus every term from $a_2$ on is the
least positive integer not used before that shares a factor greater than $1$ with the
previous term.

The indexing starts at $0$, so the source's $a_1 = 1$ and $a_2 = 2$ are $a_0$ and $a_1$ here.
The sequence begins $1, 2, 4, 6, 3, 9, 12, 8, 10, 5, \dots$

## Sources

- JIS source `hofman1.tex`, lines 99–100, <https://cs.uwaterloo.ca/journals/JIS/VOL11/Hofman/hofman1.tex>; first terms at lines 104–112.
