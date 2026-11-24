# Uniform Brun–Titchmarsh bound

Write $\pi(X; k, \ell)$ for the number of primes $p \le X$
with $p \equiv \ell \pmod{k}$, and $\varphi$ for Euler's totient function. For every real $\beta$
with $0 < \beta < 1$ there is a real constant $\xi_1 > 0$ such that for all natural numbers $X$,
$k$ and $\ell$ with $X \ge 2$, $k \ge 1$ and $k \le X^{\beta}$,

$$
\pi(X; k, \ell) < \frac{\xi_1 X}{\varphi(k) \log(X/k)}.
$$

No coprimality of $k$ and $\ell$ is assumed.

The proof applies Selberg's $\Lambda^2$ upper-bound sieve to the arithmetic progression, with
optimized weights and a harmonic lower bound for the diagonal sum.

## Sources

- Jean-Marie De Koninck and Imre Kátai, "Some Remarks on a Paper of L. Toth," Journal of Integer Sequences 13 (2010), <https://cs.uwaterloo.ca/journals/JIS/VOL13/DeKoninck/dekoninck7.tex>, Lemma, lines 424–429. The source cites E. C. Titchmarsh, "A divisor problem," Rend. Palermo 54 (1930), 414–429 and 57 (1933), 478–479. The bound `2 ≤ X` makes the source's implicit analytic lower range explicit, and the source prints no coprimality hypothesis.
