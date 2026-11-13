# Generating function of negative-index poly-Bernoulli numbers

For natural numbers $n, k$
let $B_{n,k} = \sum_{j=0}^{\min(n,k)} (j!)^2 \, S(n+1, j+1) \, S(k+1, j+1)$, where $S$ denotes
the Stirling numbers of the second kind. Then for all real numbers $x, y$ with
$(e^{|x|} - 1)(e^{|y|} - 1) < 1$,

$$\sum_{n=0}^{\infty} \left( \sum_{k=0}^{\infty} B_{n,k} \frac{x^n}{n!} \frac{y^k}{k!} \right) =
\frac{e^{x+y}}{e^x + e^y - e^{x+y}}.$$

By Kaneko's closed formula, $B_{n,k}$ is the poly-Bernoulli number $B_n^{(-k)}$ of negative
index. The condition $(e^{|x|} - 1)(e^{|y|} - 1) < 1$ is the domain of absolute convergence of
the double series (all $B_{n,k} \ge 0$). The weaker condition $|(e^x - 1)(e^y - 1)| < 1$ does
not suffice: at $x = -3$, $y = \log 1.9$ the outer series diverges.

Proof: The Stirling EGF is derived from the finite-difference formula, then absolute convergence
permits a Fubini rearrangement and a geometric-series sum, following Hamahata–Masubuchi,
Theorems 2 and 4, and Kaneko's original formula.

## Sources

- Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers," Journal of Integer Sequences 10 (2007), Article 07.4.1, Theorem 4 (symmetric formula), lines 180–186, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>; the closed formula identifying `B` is Theorem 2 there, lines 156–166. Both are attributed there to M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des Nombres de Bordeaux 9 (1997), 221–228.
