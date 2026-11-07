# Bisection method: nested intervals

Let $f : \mathbb{R} \to \mathbb{R}$ be continuous on
$[a, b]$, where $a \le b$ and $f(a) \le 0 \le f(b)$. Then there is a bisection sequence $u, v$
for $f$ from $a$ to $b$ such that for every $n \in \mathbb{N}$:
$u_n \le u_{n+1} \le v_{n+1} \le v_n$, $v_n - u_n = (b - a)/2^n$, and $f(u_n)\,f(v_n) \le 0$.

Proof: The endpoint pairs are defined recursively by the sign of each midpoint, and induction
proves the nesting, sign, and exact halving invariants from Burden and Faires, Section 2.1.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entry `bisection method` (unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed., Section 2.1; stable ref https://en.wikipedia.org/wiki/Bisection_method.
