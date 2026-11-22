# Brun–Titchmarsh inequality

Let $X$, $q$ and $a$ be natural numbers such that $a$ and $q$
are coprime and $1 \le q < X$. Write $\pi(X; q, a)$ for the number of primes $p \le X$ with
$p \equiv a \pmod{q}$, and $\varphi$ for Euler's totient function. Then

$$
\pi(X; q, a) \le \frac{2X}{\varphi(q) \log(X/q)}.
$$

The proof uses an elementary Eratosthenes sieve when $X \le 20000q$. For larger $X$ it combines
the weighted arithmetic large sieve with explicit lower bounds for the squarefree-totient sum and
the choice $z = \lfloor \sqrt{2N/3} \rfloor$, where $N = \lfloor X/q \rfloor + 1$.

## Sources

- H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004, Theorem 6.6; quoted as equation (1) in Y. Wang and X. Zhang, arXiv:2608.19262v1.
