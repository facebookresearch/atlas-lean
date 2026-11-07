# Shankar–Yuan Hessian estimate for the sigma-2 equation in dimension four

There is a function
$C : [0, \infty] \to \mathbb{R}$ with the following property. Let $B_1(0)$ be the open unit ball in
$\mathbb{R}^4$, and let $u : \mathbb{R}^4 \to \mathbb{R}$ be smooth ($C^\infty$) on $B_1(0)$ with
finite $C^1$ norm $\|u\|_{C^1(B_1(0))}$ with respect to Lebesgue measure. Suppose that for every
$x \in B_1(0)$ the Laplacian satisfies $\Delta u(x) > 0$ and the Hessian operator $Hu(x)$ of $u$
within $B_1(0)$ satisfies $\sigma_2(Hu(x)) = 1$, where $\sigma_2$ of a symmetric operator is the
second elementary symmetric function of its eigenvalues and $\sigma_2$ of a non-symmetric operator
is $0$. Then the Frobenius norm of the Hessian operator at the origin satisfies
$\|Hu(0)\|_F \le C(\|u\|_{C^1(B_1(0))})$.

## Sources

- R. Shankar and Y. Yuan, `Hessian estimates for the sigma-2 equation in dimension four`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-HessianEstimates.lean Via leanprover/lean-eval@38361be, problem `annals_hessian_estimates`.
