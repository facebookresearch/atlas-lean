# Selberg's upper bound sieve

For all real numbers $\kappa > 0$ and $C_0$ there is a
constant $C$ with the following property. Let $P$ be a set of primes, $\omega$ a non-negative
multiplicative arithmetic function with $\omega(p) < p$ for $p \in P$, $A$ a finite multiset of
positive integers, and $X > 0$ and $z \ge 2$ real numbers such that
$|\sum_{p \in P,\ t \le p < z} \omega(p) \log p / p - \kappa \log(z/t)| \le C_0$ for every real
$t$ with $2 \le t \le z$. Write $P(z) = \prod_{p \in P,\ p < z} p$, let $S$ be the number of
elements of $A$ coprime to $P(z)$ and $\#A_d$ the number of elements of $A$ divisible by $d$, both
counted with multiplicity, and let $\nu(d)$ be the number of distinct prime factors of $d$. Then
$S \le X e^{\gamma\kappa} \Gamma(\kappa + 1) \prod_{p \in P,\ p < z} (1 - \omega(p)/p)
(1 + C / \log z) + \sum_{d \mid P(z),\ d < z^2} 3^{\nu(d)} |\#A_d - \omega(d) X / d|$,
where $\gamma$ is the Euler–Mascheroni constant.

## Sources

- Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity Problem*, INTEGERS 26 (2026), Article A117, Lemma 2.
