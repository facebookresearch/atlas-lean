# Nonnegativity of trace polynomials on symmetric matrices of all sizes is undecidable

No algorithm decides whether a polynomial in traces of powers of several matrix variables is nonnegative on all tuples of real symmetric matrices of every size, even using only the traces of second, fourth and sixth powers; with normalized traces the problem becomes decidable.

**Setting (Acevedo, Blekherman, Debus and Riener).** For a variable $X$, $\operatorname{Tr}(X^m)$ denotes a formal trace symbol. A *trace polynomial* in the variables $X_1, \dots, X_k$ is a polynomial expression in the formal symbols $\operatorname{Tr}(X_i^m)$, $1 \le i \le k$, $m \ge 1$; it is evaluated on square matrices of any common size by replacing each symbol with the trace of the corresponding power. A trace polynomial $f$ is *nonnegative* if $f(A_1, \dots, A_k) \ge 0$ for all real symmetric matrices $A_1, \dots, A_k$ of all sizes $n \times n$, $n \ge 1$. The input of the decision problem is $k$ and the trace polynomial $f$, given explicitly with rational coefficients.

**Theorem (Acevedo, Blekherman, Debus and Riener).** The following problem is undecidable: given a positive integer $k$ and a trace polynomial $f(X_1, \dots, X_k)$, is $f(M_1, \dots, M_k) \ge 0$ for all real symmetric matrices $M_1, \dots, M_k$ of all sizes? The problem remains undecidable when only the symbols $\operatorname{Tr}(X_i^2)$, $\operatorname{Tr}(X_i^4)$, $\operatorname{Tr}(X_i^6)$ occur (Theorem 6.2 of arXiv:2303.09512v2).

For matrices of one fixed size the problem is decidable, by Artin's solution of Hilbert's seventeenth problem as the source recalls. If the trace is replaced by the normalized trace $\frac{1}{n}\operatorname{Tr}(A)$ of an $n \times n$ matrix, nonnegativity on symmetric matrices of all sizes is decidable (Theorem 6.5 of the source).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Since $\operatorname{Tr}(A^m) = p_m(\lambda)$ is the $m$-th power sum of the eigenvalues of $A$, nonnegativity of a trace polynomial is nonnegativity of a polynomial in power sums of $k$ groups of variables of arbitrary lengths. After normalizing homogeneous polynomials, this becomes nonnegativity of a polynomial on $(\Pi_3)^k$, where $\Pi_3$ is the closure of the union over $n$ of the images of the probability simplex under $(p_2, p_3)$, the limit Vandermonde cell. The source shows that the lower boundary of the image of the infinite probability simplex under $(2e_2, 6e_3)$ coincides with that of the set $R$ used by Hatami and Norin, with vertices $\left(\frac{n-1}{n}, \frac{(n-1)(n-2)}{n^2}\right)$ (Theorem 6.6, undecidability of nonnegativity of multihomogeneous product symmetric functions on $\Delta^k$). Following Hatami and Norin, nonnegativity of an integer polynomial on $\mathbb{N}^k$, undecidable by Matiyasevich's theorem, reduces to nonnegativity on $R^k$ and so to the trace problem. A complete expansion links a page for the reduction of Hatami and Norin (undecidability of linear inequalities between graph homomorphism densities, through nonnegativity of polynomials on the set $R^k$), which has none on main.

## Sources

- J. Acevedo, G. Blekherman, S. Debus and C. Riener, "The Wonderful Geometry of the Vandermonde map", *Foundations of Computational Mathematics* 26(4):2005–2051, 2026 (online 2025), doi:[10.1007/s10208-025-09718-6](https://doi.org/10.1007/s10208-025-09718-6); read as arXiv:2303.09512v2 ([arXiv](https://arxiv.org/abs/2303.09512v2)), whose numbering is used: the definitions of Section 6, Theorems 6.2, 6.5 and 6.6, and the proof of Theorem 6.2.
- H. Hatami and S. Norin, "Undecidability of linear inequalities in graph homomorphism densities", *Journal of the American Mathematical Society* 24(2):547–565, 2011, doi:[10.1090/S0894-0347-2010-00687-X](https://doi.org/10.1090/S0894-0347-2010-00687-X), whose reduction is adapted; not read, cited beside the source above.
