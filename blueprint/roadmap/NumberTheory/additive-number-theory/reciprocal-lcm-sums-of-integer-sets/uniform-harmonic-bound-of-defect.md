# Harmonic sums of sets with small gcd defect

For a set $A$ of natural numbers and a real
number $x$, let $S_A(x)$ be the sum of $1/n$ over $n \in A$ with $1 \le n \le x$, and let the
defect of $A$ at $x$ be the sum of $\gcd(n, m)/(nm)$ over $n, m \in A$ with $1 \le n, m \le x$,
divided by $S_A(x)^2$, minus $1$ (the defect is $-1$ when $S_A(x) = 0$). Let
$\operatorname{Log} x = \max(\log x, 1)$ be the truncated logarithm, let
$\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$ and let
$\operatorname{Log}_3 x = \operatorname{Log}(\operatorname{Log}_2 x)$. For every real
$C_0 > 0$ there are a function $e : \mathbb{R} \to \mathbb{R}$ with $e(x) \to 0$ as
$x \to \infty$ and a real $x_0$ such that for every real $x \ge x_0$ and every set $A$ of natural
numbers whose defect at $x$ is at most $C_0^2$,

$$S_A(x) \le \exp\bigl((C_0 + e(x)) (\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x\bigr).$$

The function $e$ and the threshold $x_0$ are chosen before $x$ and $A$, so the $o(1)$ error is
uniform in $A$.

## Sources

- Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*, INTEGERS 24 (2024), Article A100, Theorem 2(ii).
