# Stable switched linear systems need Lyapunov functions of unbounded complexity

For every degree $d$ there is a finite set of $47\times47$ matrices whose switched linear system is stable under arbitrary switching but has no polynomial Lyapunov function of degree $d$; no fixed degree suffices to certify stability in this dimension.

**Setting.** A finite set $\Sigma=\{A_1,\dots,A_m\}$ of real $n\times n$ matrices defines the switched linear system $x_{k+1}=A_{\sigma(k)}x_k$, where the switching signal $\sigma$ chooses one matrix at each step. The system is *absolutely asymptotically stable* (AAS) if every trajectory tends to $0$ for every switching signal; this holds exactly when the *joint spectral radius* $\rho(\Sigma)$, the limit as $k\to\infty$ of $\max\{\|A_{i_1}\cdots A_{i_k}\|^{1/k}\}$ over products of length $k$, is less than $1$. A homogeneous polynomial $p$ of even degree $d$ is a *polynomial Lyapunov function* for $\Sigma$ if $p(x)>0$ and $p(x)-p(A_ix)>0$ for all $x\neq0$ and all $i$; every AAS system has one of some degree.

**Theorem (Ahmadi and Jungers).** For every positive integer $d$ there is a finite set $\Sigma$ of $47\times47$ matrices that is AAS but has no polynomial Lyapunov function of degree $d$ (Theorem 7 of the source, part (i)).

The source's Theorem 7 states the same for the other classes of Lyapunov functions defined in its introduction: polytopic Lyapunov functions $\max_{i}|c_i^{\mathsf T}x|$ with $d$ facets, and pointwise maxima or minima of $d$ positive definite quadratic forms ($d$ pieces). For every positive integer $d$ there are AAS pairs of $2\times2$ matrices with no polynomial Lyapunov function of degree at most $d$ and none of the other three kinds with at most $d$ facets or pieces (Theorem 1 of the source), so no bound depending only on the dimension and the number of matrices exists. The source explains this by the fact that the set of stable pairs of $2\times2$ matrices is not semialgebraic (Theorem 3), while the set of pairs with a certificate of bounded complexity is (Theorem 4). For polynomial Lyapunov functions an explicit example is the normalized family of Corollary 1: the pairs $\{A_1/\rho, \alpha A_2/\rho\}$ with $A_1=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, $A_2=\begin{pmatrix}1&0\\1&1\end{pmatrix}$ and $\rho$ the joint spectral radius of $\{A_1, \alpha^* A_2\}$, $\alpha^*\approx0.7493$, contain for every $d$ an AAS pair, for some $\alpha<\alpha^*$, with no polynomial Lyapunov function of degree at most $d$.

## Depends on

None.

## Proof depends on

- [Quantifier elimination preserves truth](../../../Logic/model-theory/quantifier-elimination-for-real-closed-fields/holds-qe.md)
- [Quantifier elimination yields quantifier-free formulas](../../../Logic/model-theory/quantifier-elimination-for-real-closed-fields/is-qf-qe.md)

## Expansion

The proof of Theorem 7 argues by contradiction. Suppose every AAS set of $47\times47$ matrices had a polynomial Lyapunov function of degree $d$, for a fixed even $d$. Since $\rho$ is homogeneous, $\rho(\Sigma)\le1$ holds exactly when $\rho((1-\varepsilon)\Sigma)<1$ for all $\varepsilon\in(0,1)$, which would then be the first-order statement over the reals, with the same degree $d$ for every $\varepsilon$: for all $\varepsilon\in(0,1)$ there is a positive definite form $p$ of degree $d$ with $p((1-\varepsilon)Ax)<p(x)$ for all $x\neq0$ and all $A\in\Sigma$. Tarski's quantifier elimination decides such statements, so $\rho(\Sigma)\le1$ would be decidable for sets of two nonnegative rational $47\times47$ matrices, contradicting the source's Theorem 8; the other three classes are handled the same way once the number of facets or pieces is fixed. A good expansion links the undecidability of $\rho(\Sigma)\le1$ for two nonnegative rational $47\times47$ matrices (Theorem 8 of the source, which cites Blondel and Canterini and Blondel and Tsitsiklis for it), and the fact that positive definite forms of a fixed degree form a semialgebraic set.

## Sources

- A. A. Ahmadi and R. M. Jungers, "Lower bounds on complexity of Lyapunov functions for switched linear systems", *Nonlinear Analysis: Hybrid Systems* 21, pp. 118–129, 2016, doi:[10.1016/j.nahs.2016.01.003](https://doi.org/10.1016/j.nahs.2016.01.003); read in arXiv:1504.03761v1 ([arXiv](https://arxiv.org/abs/1504.03761v1)), in the numbering of that version: the switched system and the classes of Lyapunov functions in Section 1 (Introduction), Theorem 1 in Section 1, Definition 2 and the AAS criterion after it and Theorems 3 and 4 in Section 2, Corollary 1 in Section 3, and Theorem 7 with its proof and Theorem 8 in Section 4.
- V. D. Blondel and J. N. Tsitsiklis, "The boundedness of all products of a pair of matrices is undecidable", *Systems & Control Letters* 41(2), pp. 135–140, 2000, doi:[10.1016/S0167-6911(00)00049-9](https://doi.org/10.1016/S0167-6911(00)00049-9), and V. D. Blondel and V. Canterini, "Undecidable problems for probabilistic automata of fixed dimension", *Theory of Computing Systems* 36(3), pp. 231–245, 2003, doi:[10.1007/s00224-003-1061-2](https://doi.org/10.1007/s00224-003-1061-2): the two works Theorem 8 of the first source cites for the undecidability of $\rho(\Sigma)\le1$ for two nonnegative rational $47\times47$ matrices; not read, so the page attributes that result only as the first source does.
