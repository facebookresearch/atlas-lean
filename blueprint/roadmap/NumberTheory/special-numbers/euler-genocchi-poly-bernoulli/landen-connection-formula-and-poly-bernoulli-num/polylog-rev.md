# Reversed recursion for Kamano's generalized multiple polylogarithm

Fix Landen data $g$,
with $g_0 = \begin{pmatrix} 1 & -1 \\ c_0 & d_0 \end{pmatrix}$ and
$g_i = \begin{pmatrix} a_i & b_i \\ c_i & d_i \end{pmatrix}$ for $1 \le i \le s$, and weights
$\beta, \gamma \in \mathbb{R}^s$. For a real matrix
$h = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ let $z\,G_h(z) \in \mathbb{R}[[z]]$ be the
power series of $\frac{cz}{a - cz} - \frac{dz}{b - dz}$, where a term whose numerator and
denominator are both $0$ is read as $0$; for $w \in \mathbb{R}^s$ let
$\Phi_w = \sum_{i=1}^s w_i \, z\,G_{g_i}(z) \in \mathbb{R}[[z]]$; and for
$f = \sum_n f_n z^n \in \mathbb{R}[[z]]$ let $I(f) = \sum_{n \ge 1} (f_n / n) z^n$, which is the
formal integral $\int_0^z f(u) \, du / u$ when $f_0 = 0$. For a finite list $\ell$ of natural
numbers, the series $L(\ell) \in \mathbb{R}[[z]]$ is defined recursively: $L(\ell) = 0$ if $\ell$
is empty or its first entry is $0$; $L((1)) = I(z\,G_{g_0}(z))$;
$L((1, r, \ell')) = I(\Phi_\gamma \cdot L((r, \ell')))$ for every natural number $r$ and list
$\ell'$; and $L((n + 2, \ell')) = I(\Phi_\beta \cdot L((n + 1, \ell')))$ for every natural
number $n$ and list $\ell'$.

Applied to the reversed list $(k_r, \dots, k_1)$ of an index $k = (k_1, \dots, k_r)$, $L$ gives
Kamano's generalized multiple polylogarithm $\mathrm{Li}_k(g; (\beta, \gamma); z)$. A list with a
zero entry anywhere gives $0$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, display (6) and the two inductive integrals before it.
