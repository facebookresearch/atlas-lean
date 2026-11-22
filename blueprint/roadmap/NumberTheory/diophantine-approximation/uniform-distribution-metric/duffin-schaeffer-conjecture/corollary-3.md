# Koukoulopoulos–Maynard Corollary 3 (Hausdorff dimension of $\mathcal{A}$)

Let $\psi$
be a function from the positive integers to $[0, 1/2]$. Let $\mathcal{A}(\psi)$ be the set of
real numbers $\alpha \in [0, 1]$ for which $|\alpha - a/q| \le \psi(q)/q$ has infinitely many
solutions with $a$ a natural number, $q$ a positive integer and $\gcd(a, q) = 1$. Let $s(\psi)$
be the infimum, taken in the nonnegative reals (where the empty set has infimum $0$), of the
real numbers $\beta \ge 0$ for which the series $\sum_{q \ge 1} \varphi(q) (\psi(q)/q)^{\beta}$
converges, where $\varphi$ is Euler's totient function. Then the Hausdorff dimension of
$\mathcal{A}(\psi)$ equals $\min(s(\psi), 1)$.

## Sources

- D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_duffin_schaeffer_conjecture` of the lean-eval benchmark.
