# No computable bound on the degree of Lyapunov functions for switched linear systems

No computable function of a finite set of rational matrices bounds the degree of a polynomial Lyapunov function proving that the switched system they define is stable, and this persists for matrices with only two distinct entry values.

**Setting.** A finite set $\Sigma=\{A_1,\dots,A_m\}$ of real $n\times n$ matrices defines the switched linear system $x_{k+1}=A_{\sigma(k)}x_k$, where the switching signal $\sigma$ chooses one matrix at each step. The system is *absolutely asymptotically stable* (AAS) if every trajectory tends to $0$ for every switching signal; this holds exactly when the *joint spectral radius* $\rho(\Sigma)$, the limit of $\max\{\|A_{i_1}\cdots A_{i_k}\|^{1/k}\}$ over products of length $k$, is less than $1$. A homogeneous polynomial $p$ of even degree $d$ is a *polynomial Lyapunov function* for $\Sigma$ if $p$ is positive definite and $p(x)-p(A_ix)>0$ for all $x\neq0$ and all $i$; every AAS system has one of some degree.

**Theorem (Ahmadi and Jungers).** There is no computable function $d(\Sigma)$ that assigns to every finite set $\Sigma$ of rational matrices a natural number such that, whenever $\rho(\Sigma)<1$, $\Sigma$ has a polynomial Lyapunov function of degree less than $d(\Sigma)$ (Corollary 4 of the source).

The source proves two related results. There is no computable function $d:\mathbb N\times\mathbb Q\to\mathbb N$ such that, for every set of $n\times n$ matrices whose entries all lie in $\{0,K\}$ with $K\in\mathbb Q$, the set is AAS exactly when it has a polynomial Lyapunov function of degree $d(n,K)$ (Theorem 10). For every positive integer $d$ there are finite sets of $47\times47$ matrices that are AAS but have no polynomial Lyapunov function of degree $d$, no polytopic Lyapunov function with $d$ facets, and no max-of-quadratics or min-of-quadratics Lyapunov function with $d$ pieces (Theorem 7).

The same paper gives constructive proofs that for every $d$ there are AAS pairs of $2\times2$ matrices with no polynomial Lyapunov function of degree at most $d$, so no bound depending only on the dimension and the number of matrices exists.

## Depends on

None.

## Proof depends on

None.

## Expansion

The proofs use the undecidability of $\rho(\Sigma)\le1$, which Blondel and Tsitsiklis proved even for two nonnegative rational $47\times47$ matrices (Theorem 8 of the source, citing them); that result has no page on main. If every AAS set of a given size had a polynomial Lyapunov function of degree at most $d$, or of degree below a computable bound $d(\Sigma)$, then $\rho(\Sigma)\le1$, which is equivalent to $\rho((1-\varepsilon)\Sigma)<1$ for all $\varepsilon\in(0,1)$, would be a first-order statement over the reals about polynomials of bounded degree, decidable by Tarski's quantifier elimination; the same works for polytopic and piecewise quadratic functions with a bounded number of pieces. Theorem 10 adds a construction of Jungers and Blondel (Theorem 9 of the source) that encodes a set of nonnegative rational matrices into a set of $0$–$1$ matrices whose joint spectral radius is a known multiple $K$ of the original. A good expansion links pages for Tarski's decision procedure for real closed fields and for the Jungers–Blondel encoding into binary matrices; neither has a page yet.

## Sources

- A. A. Ahmadi and R. M. Jungers, "Lower bounds on complexity of Lyapunov functions for switched linear systems", *Nonlinear Analysis: Hybrid Systems* 21, pp. 118–129, 2016, doi:[10.1016/j.nahs.2016.01.003](https://doi.org/10.1016/j.nahs.2016.01.003); read in arXiv:1504.03761v1 ([arXiv](https://arxiv.org/abs/1504.03761v1)): the problem setting and classes of Lyapunov functions in the introduction, and Theorems 7, 8, 9 and 10 and Corollary 4 in Section 4 of arXiv:1504.03761v1.
