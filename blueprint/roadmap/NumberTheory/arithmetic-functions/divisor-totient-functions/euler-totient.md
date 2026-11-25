# Euler's totient function

For a natural number $n$, *Euler's totient* $\varphi(n)$ is the number of integers $m$ with $0 \le m < n$ and $\gcd(m, n) = 1$. For $n \ge 1$ this is also the number of integers $m$ with $1 \le m \le n$ and $\gcd(m, n) = 1$: for $n = 1$ both counts are $1$, and for $n \ge 2$ neither $0$ nor $n$ is coprime to $n$. In particular $\varphi(1) = 1$, and $\varphi(0) = 0$.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the count over $0 \le m < n$: `Nat.totient`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/Nat/Totient.lean#L35-L38.
