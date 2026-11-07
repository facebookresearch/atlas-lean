# Baby version of the dense-set construction

Let $e$ be Euler's number, let
$\operatorname{Log}_2$ and $\operatorname{Log}_3$ be the second and third iterated truncated
logarithms, and for a set $B$ of natural numbers and real $x$ write
$S_B(x) = \sum_{n \in B,\ 1 \le n \le x} 1/n$ and $\mathcal{E}_B(x)$ for the gcd defect of $B$ up
to $x$. There is an absolute constant $C > 0$ such that for every real $C_0 > 0$ there are sets
$A_0, A_1, A_2, \dots$ of natural numbers with the following property: for every $\varepsilon > 0$
there are a real $\delta > 0$ and a natural number $k_0$ such that for every natural number
$k \ge k_0$ and every real $x$ with $|C_0 (\operatorname{Log}_2 x)^{1/2} - k| \le \delta k$, there
is a real $\eta$ with $|\eta| \le \varepsilon$ and
$S_{A_k}(x) = \exp((C_0/2 + \eta)(\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x)$, and
moreover $\mathcal{E}_{A_k}(x) \le C(\exp(e^2 C_0^2) - 1 + \varepsilon)$.

In the source this is Proposition 1, a simplified version of the construction for Theorem 2(i)
(its lead-in sentence refers to Theorem 2(ii)): the sets $A_k$ satisfy (31) and the bound (21)
in the range (32), with all $o(1)$ terms taken as $k \to \infty$. Above, these $o(1)$ terms are
written with $\varepsilon$, $\delta$ and $k_0$.

## Sources

- Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*, INTEGERS 24 (2024), Article A100, Proposition 1, (31) and (32), with (21) (`integers-2024-A100-prop-1`).
