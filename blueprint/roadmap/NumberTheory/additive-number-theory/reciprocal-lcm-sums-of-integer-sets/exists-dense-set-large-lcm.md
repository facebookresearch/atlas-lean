# Dense sets with unusually large least common multiples

Let $\operatorname{Log}_2$ and
$\operatorname{Log}_3$ be the second and third iterated truncated logarithms. For a set $A$ of
natural numbers and real $x$, write $S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$, and write
$L_A(x)$ for the sum of $1/\operatorname{lcm}(n, m)$ over all ordered pairs $(n, m)$ with
$n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$. Then for every real $C_0 > 0$ there is a set
$A$ of natural numbers with the following two properties. First, there is a function
$\varepsilon : \mathbb{R} \to \mathbb{R}$ with $\varepsilon(x) \to 0$ as $x \to \infty$ such that
for all sufficiently large real $x$,
$S_A(x) = \exp((C_0/2 + \varepsilon(x))(\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x)$.
Second, there is a constant $K > 0$ such that $L_A(x) \le K\, S_A(x)^2$ for all sufficiently
large real $x$.

The source presents this as a negative answer to Erdős problem #442. Its accompanying claim that
the exponent is optimal is made precise by Theorem 2(ii) and is stated separately.

## Sources

- Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*, INTEGERS 24 (2024), Article A100, Theorem 1.
