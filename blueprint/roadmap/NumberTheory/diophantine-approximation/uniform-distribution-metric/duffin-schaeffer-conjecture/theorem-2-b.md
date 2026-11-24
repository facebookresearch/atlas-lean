# Koukoulopoulos–Maynard Theorem 2(b) (Catlin's conjecture, divergent case)

Let $\psi$
be a function from the positive integers to the nonnegative reals, and for each positive integer
$q$ let $\psi^*(q) = \varphi(q) \cdot \sup \{\psi(n)/n : n \text{ a positive integer with }
q \mid n\}$, where $\varphi$ is Euler's totient function and the supremum is taken in
$[0, \infty]$. Let $\mathcal{K}(\psi)$ be the set of real numbers $\alpha \in [0, 1]$ for which
$|\alpha - a/q| \le \psi(q)/q$ has infinitely many solutions with $a$ a natural number and $q$ a
positive integer such that $a \le q$. If $\sum_{q \ge 1} \psi^*(q) = \infty$, then
$\mathcal{K}(\psi)$ is a Borel set and has Lebesgue measure $1$.

## Sources

- D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_duffin_schaeffer_conjecture` of the lean-eval benchmark.
