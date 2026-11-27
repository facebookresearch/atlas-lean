# Identifiable reparametrization of rational ODE models

**Setting.** A parametric ODE model

$$\Sigma(\bar\alpha):\quad \bar x'=\bar f(\bar x,\bar\alpha,\bar u),\qquad \bar y=\bar g(\bar x,\bar\alpha,\bar u),$$

has states $\bar x$, unknown parameters $\bar\alpha$, inputs $\bar u$, outputs $\bar y$, and rational right-hand sides over $\mathbb Q(\bar\alpha)$. Its *input-output (IO) equations* are the differential polynomial relations among $\bar y,\bar u$ and their derivatives obtained by eliminating $\bar x$; a parameter function is (locally or globally) *IO-identifiable* if it is determined, locally or uniquely, by the coefficients of the IO-equations. The **identifiable reparametrization problem** asks for new parameters $\bar\beta$, algebraic over $\mathbb Q(\bar\alpha)$, and new states $\bar w$, algebraic over $\mathbb Q(\bar x,\bar\alpha,\bar u,\bar u',\dots)$, with $|\bar w|=|\bar x|$, such that $\bar w'=\bar F(\bar w,\bar\beta,\bar u,\dots)$, $\bar y=\bar G(\bar w,\bar\beta,\bar u,\dots)$ for rational $\bar F,\bar G$, every entry of $\bar\beta$ is at least locally IO-identifiable, and the new system has the same IO-equations as $\Sigma(\bar\alpha)$.

**Theorem 1 (algorithm).** There is an algorithm solving the local IO-identifiable reparametrization problem for every such rational model. If the orders of the IO-equations in the outputs sum to the dimension of the model, the new states are algebraic functions of $\bar x$ and $\bar\alpha$; and if a globally IO-identifiable reparametrization exists whose Lie derivatives have monomial support contained in that of the original model's Lie derivatives, the algorithm finds it.

**Theorem 2 (linear models).** Every model in which $\bar f$ and $\bar g$ are linear has a globally IO-identifiable reparametrization obtained by a linear change of state variables, and the algorithm finds it.

**Theorem 3 (single-output linear compartmental models).** Let $\bar x'=A\bar x$, $y=x_1$, where the directed graph of $A$ is strongly connected and has at least one leak. With $p^{(k)}_{1j}$ the sum over all directed paths of length $k$ from compartment $j$ to compartment $1$ of the products of the corresponding entries of $A$, set $X_1=x_1$ and $X_i=\sum_{j=1}^n p^{(i-1)}_{1j}x_j$ for $i=2,\dots,n$; equivalently $\bar X=P\bar x$ with $P$ the observability matrix with rows $C,CA,\dots,CA^{n-1}$. Then

$$X_1'=X_2,\ \dots,\ X_{n-1}'=X_n,\qquad X_n'=-c_0X_1-c_1X_2-\dots-c_{n-1}X_n,\qquad y=X_1,$$

where $c_0,\dots,c_{n-1}$ are the non-leading coefficients of the characteristic polynomial of $A$. This system is globally IO-identifiable (hence globally identifiable), and the $X_i$ are linearly independent (Corollary 1). Theorems 4 and 5 give the analogous observability-matrix reparametrizations for several measured compartments and for a single input and output.

## Expansion

The IO-equations of a model depend on $\bar\alpha$ only through finitely many coefficient functions; these generate the field of IO-identifiable functions, so the task is to rewrite the dynamics with parameters in that field. The algorithm computes Lie derivatives of the outputs along the vector field, uses them to pick new states as combinations that are expressible through identifiable coefficients, and checks that the Jacobian of the change of variables is non-degenerate. For linear single-output models the successive output derivatives are $CA^{k}\bar x$, so taking them as states yields the companion (observable canonical) form, whose only parameters are the characteristic-polynomial coefficients; these are exactly the coefficients of the IO-equation $y^{(n)}+c_{n-1}y^{(n-1)}+\dots+c_0y=0$ and are therefore globally identifiable.

## Sources

- N. Meshkat, A. Ovchinnikov, T. Scanlon, "Algorithm to find new identifiable reparametrizations of parametric rational ODE models", *IEEE Transactions on Automatic Control* 70(10) (2025), 6688–6703, Theorems 1-5 and Corollary 1, <https://doi.org/10.1109/tac.2025.3565058> (preprint arXiv:2310.03057).
