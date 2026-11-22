# Scottish Book Problem 74: the coefficient bound holds

Let $n \ge 1$, let $a_k$ be real
coefficients indexed by multi-indices $k = (k_1, \dots, k_n) \in \mathbb{N}^n$, and let
$P(t) = \sum_{k_1 + \cdots + k_n = n} a_k \, t_1^{k_1} \cdots t_n^{k_n}$ be the corresponding
homogeneous polynomial of degree $n$ on $\mathbb{R}^n$. If $|P(t)| \le 1$ for every
$t \in \mathbb{R}^n$ with $|t_1| + \cdots + |t_n| \le 1$, then
$|a_k| \le n^n / (k_1! \cdots k_n!)$ for every $k \in \mathbb{N}^n$ with
$k_1 + \cdots + k_n = n$.

Proof: Let $L$ be the symmetric $n$-linear form with $L(t, \dots, t) = P(t)$. The polarization
identity gives

$$L(x_1, \dots, x_n) = \frac{1}{2^n n!} \sum_{\varepsilon \in \{\pm 1\}^n} \varepsilon_1 \cdots \varepsilon_n \, P\Big(\sum_i \varepsilon_i x_i\Big).$$

Take $x_1, \dots, x_n$ to be $e_1$ repeated $k_1$ times, ..., $e_n$ repeated $k_n$ times. Then
$a_k = \frac{n!}{k_1! \cdots k_n!} L(x_1, \dots, x_n)$ and $\|\sum_i \varepsilon_i x_i\|_1 \le n$, so
$|P(\sum_i \varepsilon_i x_i)| \le n^n$ by homogeneity. Hence $|L(x_1, \dots, x_n)| \le n^n / n!$ and
$|a_k| \le n^n / (k_1! \cdots k_n!)$.

The open part of Problem 74 is the exact best constant
$C^*(n, k) = \sup \{ |a_k| : |P(t)| \le 1 \text{ whenever } \|t\|_1 \le 1 \}$, for which no closed form
is known. The bound above is not sharp for every $k$: for $k = (n, 0, \dots, 0)$ with $n \ge 2$ the
best constant is $1$ (since $|a_k| = |P(e_1)| \le 1$), while $n^n / n! > 1$. The monomial
$t_1^{k_1} \cdots t_n^{k_n}$ gives the lower bound $C^*(n, k) \ge n^n / (k_1^{k_1} \cdots k_n^{k_n})$, with
$0^0 = 1$.

## Sources

- S. Mazur and W. Orlicz, Problem 74 of the Scottish Book; typescript PDF p.36, printed p.33; see the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015). Proved by the classical polarization identity; the Rademacher form is Lemma 12 of M. Chatzakou and Y. Sarantopoulos, "Estimates for polynomial norms on Banach spaces", arXiv:2107.05993.
