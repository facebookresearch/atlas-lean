# Normally hyperbolic curve of equilibria of the ribosome flow model with pool

**Model.** The ribosome flow model (RFM) with pool describes translation of an mRNA discretized into $n$ sites, each holding at most one ribosome, coupled to a finite pool of free ribosomes. With free-ribosome amount $R \ge 0$, site densities $x_i \in [0,1]$, initiation rate $\lambda > 0$ and elongation rate $\lambda_c > 0$,

$$ \dot R = -\lambda R (1 - x_1) + \lambda_c x_n, \qquad \dot x_1 = \lambda R (1 - x_1) - \lambda_c x_1 (1 - x_2), $$

$$ \dot x_i = \lambda_c x_{i-1} (1 - x_i) - \lambda_c x_i (1 - x_{i+1}) \quad (2 \le i \le n-1), \qquad \dot x_n = \lambda_c x_{n-1} (1 - x_n) - \lambda_c x_n. $$

Write $\mathbf{x} = (R, x_1, \dots, x_n)$ and $\dot{\mathbf{x}} = f(\mathbf{x})$ on $\Omega = [0,\infty) \times [0,1]^n$.

**Equilibria.** The equilibria in the interior of $\Omega$ form a curve $\gamma(s) = (\gamma_0(s), \dots, \gamma_n(s))$, $s \in (0, \bar s)$, given by the continued fractions

$$ \gamma_n(s) = s, \qquad \gamma_i(s) = \frac{s}{1 - \gamma_{i+1}(s)} \ (1 \le i \le n-1), \qquad \gamma_0(s) = \frac{\lambda_c\, s}{\lambda\,(1 - \gamma_1(s))}, $$

where $s = x_n$ is the normalized protein production rate (the output flux is $\lambda_c s$) and $\bar s$, depending only on $n$, is the root of $1 + \sum_{j=0}^{\lfloor (n-1)/2 \rfloor} (-\bar s)^{j+1} \binom{n-j}{j+1} = 0$ bounding the attainable production rate by $\lambda_c \bar s$.

**Theorem.**

1. (Theorem 1) For every $s \in (0, \bar s)$, the Jacobian $J_f(\gamma(s))$ has a simple eigenvalue $0$ and all other eigenvalues have strictly negative real parts.
2. (Lemma 1) The eigenvector of the zero eigenvalue is parallel to $\dot\gamma(s)$, i.e. tangent to the curve of equilibria.
3. (Proposition 1, Lemma 2) The total ribosome number $\sum_{i=0}^{n} x_i$ is conserved, so each affine hyperplane $S_p = \{ \sum_i x_i = p \}$ is invariant, with $p = R_{\mathrm{tot}}$; for every $p > 0$ the curve $\gamma$ meets $S_p$ in exactly one point, transversally.
4. (Theorem 2) The invariant set $\gamma((0, \bar s))$ is normally hyperbolic and asymptotically stable; in particular, for each total ribosome amount $R_{\mathrm{tot}} > 0$ the unique equilibrium in $S_{R_{\mathrm{tot}}}$ is asymptotically stable relative to $S_{R_{\mathrm{tot}}}$.

## Expansion

Writing $f(\mathbf{x}) = A(\mathbf{x}) \mathbf{x}$ with a compartmental (Metzler, zero column sum) matrix $A$, equilibria are the points with $\mathbf{x} \in \ker A(\mathbf{x}) = \operatorname{span}\bigl(\lambda_c / (\lambda(1-x_1)), 1/(1-x_2), \dots, 1/(1-x_n), 1\bigr)$, and solving recursively gives the continued fractions. Conservation of $\sum_i x_i$ means the column sums of the Jacobian vanish, which forces the zero eigenvalue; the tangent vector $\dot\gamma$ spans its eigenspace, and the remaining eigenvalues are shown to have negative real parts, so the normal directions are contracting. Since the equilibria are not hyperbolic, Lyapunov's indirect method does not apply directly; instead the normally hyperbolic invariant manifold theory of Hirsch, Pugh and Shub conjugates the flow near the curve to its linearization on the normal bundle, and transversality to the invariant hyperplanes $S_p$ turns this into asymptotic stability of each equilibrium within its level set. The argument uses no monotonicity, unlike earlier proofs based on monotone systems theory.

## Sources

- Wolfgang Halter, Jan Maximilian Montenbruck, Frank Allgöwer, "Geometric stability considerations of the ribosome flow model with pool", in Proceedings of the 22nd International Symposium on Mathematical Theory of Networks and Systems (MTNS 2016), <http://hdl.handle.net/11299/181518> (the proceedings have no DOI). Published version of arXiv:1610.03986, cited next; locators there refer to the arXiv version.
- Wolfgang Halter, Jan Maximilian Montenbruck, Frank Allgöwer, "Geometric stability considerations of the ribosome flow model with pool", arXiv (2016). Section 3, Theorem 1, Lemma 1, Proposition 1, Lemma 2, Theorem 2, and the appendix derivation of $\bar s$. <https://doi.org/10.48550/arXiv.1610.03986>
