# Nonnegativity of a cyclically invariant polynomial for all system sizes is undecidable

No algorithm decides, given finitely many integer polynomials $p_{\alpha,\beta}$ that are combinations of squares of variables, whether the cyclically invariant polynomials $p_n$ they generate are nonnegative, or sums of squares, for every system size $n$; this holds already with $m, D \ge 7$.

**Setting (De las Cuevas, Klingler and Netzer).** Given positive integers $m$ and $D$ and polynomials $p_{\alpha,\beta} \in \mathbb{Z}[x_1, \dots, x_m]$ for $\alpha, \beta \in \{1, \dots, D\}$, let $\mathbf{x}^{[0]}, \dots, \mathbf{x}^{[n]}$ be $n + 1$ disjoint copies of the variables $\mathbf{x} = (x_1, \dots, x_m)$ and

$$
p_n = \sum_{\alpha_0, \dots, \alpha_n = 1}^{D} p_{\alpha_0, \alpha_1}(\mathbf{x}^{[0]})\, p_{\alpha_1, \alpha_2}(\mathbf{x}^{[1]}) \cdots p_{\alpha_n, \alpha_0}(\mathbf{x}^{[n]}) \in \mathbb{R}[\mathbf{x}^{[0]}, \dots, \mathbf{x}^{[n]}],
$$

a polynomial invariant under cyclic shifts of the copies. The input of the decision problem is $m$, $D$ and the family $(p_{\alpha,\beta})$.

**Theorem (De las Cuevas, Klingler and Netzer).** The following two problems are undecidable (Theorem 51 of arXiv:2109.06680v2):

1. is $p_n$ a sum of squares of polynomials for all $n \in \mathbb{N}$?
2. is $p_n$ nonnegative on all of $\mathbb{R}^{m(n+1)}$ for all $n \in \mathbb{N}$?

Both remain undecidable when $m, D \ge 7$ and every $p_{\alpha,\beta}$ has the form $\sum_{j=1}^m c_{\alpha,\beta,j} x_j^2$ with $c_{\alpha,\beta,j} \in \mathbb{Z}$.

The source notes that the bounded version of these questions, with $n$ fixed, is NP-hard. Allowing rational coefficients does not change the result, since positive scaling preserves both properties.

## Depends on

None.

## Proof depends on

None.

## Expansion

The proof reduces from the undecidability, due to De las Cuevas, Cubitt, Cirac, Wolf and Pérez-García, of deciding, for vectors $T_{\alpha,\beta} \in \mathbb{Z}^m$ with $m, D \ge 7$, whether all tensors $T_n = \sum T_{\alpha_0,\alpha_1} \otimes \cdots \otimes T_{\alpha_n,\alpha_0}$ have nonnegative entries. Setting $p_{\alpha,\beta} = \sum_j (T_{\alpha,\beta})_j x_j^2$, the polynomial $p_n$ is the sum of the entries of $T_n$ times the corresponding monomials in squares of variables, and the source's correspondence lemma shows that $p_n$ is a sum of squares exactly when it is nonnegative, exactly when every entry of $T_n$ is nonnegative. A complete expansion links a page for that tensor-positivity theorem (positivity of translation-invariant matrix product operators for all system sizes), which has none on main.

## Sources

- G. De las Cuevas, A. Klingler and T. Netzer, "Polynomial decompositions with invariance and positivity inspired by tensors", *Linear Algebra and its Applications* 698:537–588, 2024, doi:[10.1016/j.laa.2024.05.025](https://doi.org/10.1016/j.laa.2024.05.025); read as arXiv:2109.06680v2 ([arXiv](https://arxiv.org/abs/2109.06680v2)), whose numbering is used: Problem 50, Theorem 51 with its proof and Theorem 52, in the section on an undecidable problem regarding unconstrained decompositions.
- G. De las Cuevas, T. S. Cubitt, J. I. Cirac, M. M. Wolf and D. Pérez-García, "Fundamental limitations in the purifications of tensor networks", *Journal of Mathematical Physics* 57:071902, 2016, doi:[10.1063/1.4954983](https://doi.org/10.1063/1.4954983), the theorem reduced from; not read, cited beside the source above.
