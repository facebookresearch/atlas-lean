# Malthus parameter of a unidirectional layered age-structured population

Cells are structured by age $a\ge0$ and distributed over layers $j=1,\dots,J$. A cell in layer $j$ divides at age-dependent rate $b_j(a)$; at division the age is reset and each daughter independently (in the mean) stays in layer $j$ with probability $p_S^{(j)}$ or moves to layer $j+1$ with probability $p_L^{(j)}=1-p_S^{(j)}$, with $p_S^{(J)}=1$ (the last layer is absorbing). The deterministic age densities $\rho^{(j)}(t,a)$ satisfy

$$ \partial_t\rho^{(j)}+\partial_a\rho^{(j)}=-b_j(a)\rho^{(j)},\qquad \rho^{(j)}(t,0)=2p_L^{(j-1)}\int_0^\infty b_{j-1}\rho^{(j-1)}\,da+2p_S^{(j)}\int_0^\infty b_j\rho^{(j)}\,da, $$

with $p_L^{(0)}=0$; the stochastic version is a multi-type Bellman–Harris branching process $Z_t$ with the same mean.

Assume $p_S^{(j)},p_L^{(j)}\in(0,1)$ for $j<J$ and $0<\underline b_j\le b_j(a)\le\overline b_j<\infty$ with $b_j$ continuous. Define the intrinsic growth rate $\lambda_j$ of layer $j$ by

$$ \int_0^\infty e^{-\lambda_js}\,b_j(s)e^{-\int_0^sb_j(u)\,du}\,ds=\frac{1}{2p_S^{(j)}}, $$

so $\lambda_j$ has the sign of $p_S^{(j)}-\tfrac12$ and $\lambda_J>0$; for constant rates $\lambda_j=(2p_S^{(j)}-1)b_j$. Assume the maximum $\lambda=\max_j\lambda_j$ is attained at a unique leading layer $c$, and $\lambda_j>-\liminf_{a\to\infty}b_j(a)$ for all $j$.

**Theorem.** The block-triangular renewal system, to which Perron–Frobenius and Krein–Rutman arguments do not apply directly, still has a unique first eigentriple $(\lambda,N,\phi)$, with $N\in L^1(\mathbb R_+)^J$ the stable age distribution and $\phi\in C_b(\mathbb R_+)^J$ the adjoint eigenfunction, and its eigenvalue is the Malthus parameter $\lambda=\max_j\lambda_j$. Every solution satisfies, layer by layer,

$$ \big\langle|e^{-\lambda t}\rho^{(j)}(t,\cdot)-\eta\hat\rho^{(j)}|,\hat\phi^{(j)}\big\rangle\le\sum_{k=1}^je^{-\mu_jt}\beta_k^{(j)}(t)\,\big\langle|\rho_0^{(k)}-\eta N^{(k)}|,\hat\phi^{(k)}\big\rangle, $$

where $\eta=\langle\rho_0,\phi\rangle$, $\beta_k^{(j)}$ are polynomials of degree at most $j-k$, $\mu_j=\lambda-\lambda_j>0$ for $j\neq c$ and $\mu_c=\underline b_c$. In the stochastic model, $e^{-\lambda t}\langle\phi,Z_t\rangle$ is a square-integrable martingale converging almost surely and in $L^2$ to a non-degenerate limit, and when all $\lambda_j$ are distinct the mean number of cells of age at most $a$ in layer $j$ grows like $e^{\lambda t}$ times an explicit constant, which is zero for the layers $j<c$ upstream of the leading layer.

## Expansion

Because cells only move downstream, the layers form a cascade: layer $j$ is a one-layer McKendrick–von Foerster equation forced by the output of layer $j-1$. Each isolated layer grows at its own rate $\lambda_j$, so the whole population grows at the fastest rate, and layers upstream of the leading one become negligible after renormalization. Convergence is proved by an entropy (conservation-principle) argument for $|h|=|e^{-\lambda t}\rho-\eta N|$ tested against per-layer adjoint functions $\hat\phi^{(j)}$, giving a triangular system of differential inequalities solved by a Grönwall lemma that produces the polynomial prefactors.

## Sources

- F. Clément, F. Robin and R. Yvinec, "Analysis and calibration of a linear model for structured cell populations with unidirectional motion: application to the morphogenesis of ovarian follicles", arXiv:1712.05372 (2017), <https://doi.org/10.48550/arXiv.1712.05372>. Section "Model description and main results": the intrinsic growth rates and the Malthus parameter (Hypothesis/Definition statements in the Hypotheses subsection), the eigenproblem theorem and the exponential convergence theorem (subsection "Eigenproblem approach"), the martingale convergence theorem, and the long-time mean theorem (subsection "Renewal equation approach"). Published version: SIAM Journal on Applied Mathematics 79 (2019) 207–229, <https://doi.org/10.1137/17m1161336>.
