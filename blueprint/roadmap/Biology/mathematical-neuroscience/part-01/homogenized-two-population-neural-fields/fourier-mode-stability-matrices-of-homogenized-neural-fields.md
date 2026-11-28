# Fourier-mode stability matrices of the homogenized two-population neural field

In the homogenized two-population neural field (see the dependency), let $U_0 = (v_0, v_0)$ be a spatially constant equilibrium and put $P_q' = P_q'(v_0 - \theta_q)$. Write $\tilde\omega_{qp}(k,y) = \tilde\Phi(k\,\sigma_{qp}(y))$ for the Fourier transform in $x$ and

$$\hat\omega_{qp}^{(n)}(\eta) = \int_{\mathbb{T}} \tilde\Phi\big(k\,\sigma_{qp}(y)\big)\, e^{-2\pi i n y}\,dy, \qquad \eta = k^2,\ n \in \mathbb{N}_0,$$

for its Fourier coefficients in the microscopic variable $y$ (real, even in $k$ and in $n$).

**Mode decomposition.** Perturbations $e^{2\pi i (kx + ny)}$ decouple, and the linearized dynamics of the mode $(k, n)$ is $\partial_t \hat V_n = A_n(\eta)\hat V_n$ with

$$A_n(\eta) = \begin{pmatrix} -1 + P_e'\hat\omega_{ee}^{(n)}(\eta) & -P_i'\hat\omega_{ie}^{(n)}(\eta)\\ \tfrac{1}{\tau}P_e'\hat\omega_{ei}^{(n)}(\eta) & -\tfrac{1}{\tau}\big(1 + P_i'\hat\omega_{ii}^{(n)}(\eta)\big)\end{pmatrix}.$$

With trace $\varphi_n = \operatorname{tr}A_n$ and determinant $\psi_n = \det A_n$, the eigenvalues are $\lambda_n^\pm = \tfrac12\big(\varphi_n \pm \sqrt{\varphi_n^2 - 4\psi_n}\big)$. The equilibrium is linearly stable if every curve $\Gamma_n(\eta) = (\varphi_n(\eta), \psi_n(\eta))$, $\eta \ge 0$, stays in the quadrant $\varphi_n < 0$, $\psi_n > 0$, and unstable if some $\Gamma_n$ leaves it on an interval of $\eta$.

**Properties.**

1. $A_0(\eta)$ equals the stability matrix of the translation-invariant field with the averaged kernels $\langle\omega_{qp}\rangle$; at $\eta = 0$ it is the Jacobian of the space-clamped system, and $A_n(0) = \operatorname{diag}(-1, -1/\tau)$ for $n \ge 1$, so $\Gamma_n(0) = (-1 - 1/\tau, 1/\tau)$ lies in the stable quadrant.
2. Each $\hat\omega_{qp}^{(n)}$ is continuous in $k$ and tends to $0$ as $|k| \to \infty$; if $\Phi$ has a finite $r$-th moment, $\hat\omega_{qp}^{(n)}$ is $r$ times continuously differentiable in $k$ and $|\hat\omega_{qp}^{(n)}(k)| \le A_{qp}(k)/n^r$ with $A_{qp}(k) = (2\pi)^{-r}\max_y |\partial_y^r \tilde\Phi(k\,\sigma_{qp}(y))|$. Thus high microscopic modes are damped and the gain band (the set of unstable wave numbers) has finite bandwidth.
3. In the translation-invariant limit ($\sigma_{qp}$ constant) all $A_n$ with $n \ge 1$ reduce to $\operatorname{diag}(-1, -1/\tau)$, and stability is decided by $A_0$ alone; for weak modulation the gain band is a continuous deformation of the translation-invariant one.

## Depends on

- [Mean-kernel approximation and global attractor of the homogenized two-population neural field](mean-kernel-approximation-of-homogenized-neural-fields.md)

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)

## Expansion

The Frechet derivative of the double-convolution operator at a constant state is $P_q'$ times convolution in both $x$ and $y$; Fourier transform in $x$ and Fourier series in $y$ diagonalize both convolutions, which yields the family of $2 \times 2$ matrices. At $k = 0$ the kernels integrate to $1$ in $x$ for every $y$, so only the $n = 0$ coefficient is nonzero. Property 1 is Fubini: the Fourier transform of $\langle\omega_{qp}\rangle$ is the $y$-average of $\tilde\omega_{qp}$, i.e. $\hat\omega_{qp}^{(0)}$. Property 2 is the Riemann-Lebesgue lemma plus $r$ integrations by parts in $y$. With the exponential kernel $\Phi(\xi) \propto e^{-|\xi|}$ one has $\tilde\Phi(k) = 1/((2\pi k)^2 + 1)$ and the coefficients become explicit $y$-integrals; the source shows numerically stationary periodic patterns for steep firing rates and spatiotemporal oscillations for shallow ones. The source also notes that a mode $n \ge 1$ might undergo a Turing or Turing–Hopf bifurcation when $n = 0$ does not, and exhibits numerically a Turing bifurcation of the $n = 1$ mode (Fig. 5); its proved Turing–Hopf result is the $n = 0$ one deformed from the translation-invariant case (Appendix C, Theorem 6).

## Sources

- K. Kolodina, J. Wyller, A. Oleynik, M. P. Sorensen, Pattern formation in a 2-population homogenized neuronal network model, Journal of Mathematical Neuroscience (2021), Section 4 (Eqs. 28 to 53, Fig. 5), Appendix B (Theorems 2 to 5, Corollary 1) and Appendix C (Theorem 6). <https://doi.org/10.1186/s13408-021-00107-1> PMCID: PMC8236021
