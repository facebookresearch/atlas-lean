# Second derivatives of population growth rates

**Setting.** Let $A$ be an $n \times n$ population projection matrix whose dominant eigenvalue $\lambda$ is simple, with right and left eigenvectors $w, v$ ($Aw = \lambda w$, $v^{\mathsf T}A = \lambda v^{\mathsf T}$) scaled so that $v^{\mathsf T}w = 1$. Let $Z = (\lambda I - A)^{\#}$ be the group inverse of $\lambda I - A$ (when $A$ is diagonalizable with eigenvalues $\lambda_m$ and eigenvector pairs $w^{(m)}, v^{(m)}$, $Z = \sum_{\lambda_m \ne \lambda} w^{(m)}v^{(m)\mathsf T}/(\lambda - \lambda_m)$). The first derivatives are $\partial\lambda/\partial a_{ij} = v_i w_j$, i.e. $D[\lambda; \operatorname{vec}A] = w^{\mathsf T}\otimes v^{\mathsf T}$.

**Hessian with respect to matrix entries.** The matrix $H[\lambda; \operatorname{vec}A]$ of second derivatives has entries

$$\frac{\partial^2\lambda}{\partial a_{ij}\,\partial a_{kl}} = v_i\,Z_{jk}\,w_l + v_k\,Z_{li}\,w_j .$$

**Hessian chain rule for lower-level parameters.** If the entries of $A$ are twice differentiable functions of parameters $\theta \in \mathbb{R}^s$, then

$$H[\lambda;\theta] = D[\operatorname{vec}A;\theta]^{\mathsf T}\,H[\lambda;\operatorname{vec}A]\,D[\operatorname{vec}A;\theta] + \sum_{m=1}^{n^2}\frac{\partial\lambda}{\partial(\operatorname{vec}A)_m}\,H[(\operatorname{vec}A)_m;\theta],$$

where the second term is $(D[\lambda;\operatorname{vec}A]\otimes I_s)\,H[\operatorname{vec}A;\theta]$ with the Hessians of the entries of $\operatorname{vec}A$ stacked.

**Invasion exponent.** For $r = \log\lambda$ and any parameter vector $x$ (entries of $A$ or $\theta$),

$$H[r;x] = \frac{1}{\lambda}H[\lambda;x] - \frac{1}{\lambda^2}D[\lambda;x]^{\mathsf T}D[\lambda;x].$$

**Net reproductive rate.** Write $A = U + F$ (survival transitions and fertilities), $N = (I - U)^{-1}$, and let $R_0$ be the dominant eigenvalue of $R = FN$. The formulas above apply with $R$ in place of $A$ and the chain rule through $R(\theta)$, using $d\,N = N\,(dU)\,N$. Since $R$ is linear in $F$, the Hessian of $\operatorname{vec}R$ with respect to $\operatorname{vec}F$ is zero. If only stage $1$ is produced as offspring, $R_0 = e_1^{\mathsf T}FNe_1$, so $R_0$ is linear in $F$ and

$$\frac{\partial^2 R_0}{\partial u_{ij}\,\partial u_{kl}} = (e_1^{\mathsf T}FN)_i\,N_{jk}\,(Ne_1)_l + (e_1^{\mathsf T}FN)_k\,N_{li}\,(Ne_1)_j .$$

## Depends on

- [Sensitivity of the population growth rate to matrix entries](eigenvalue-sensitivity-formula.md)

## Expansion

For a perturbation $A + \epsilon E$ of a simple eigenvalue, $\lambda(\epsilon) = \lambda + \epsilon\,v^{\mathsf T}Ew + \epsilon^2\,v^{\mathsf T}EZEw + O(\epsilon^3)$; polarizing the quadratic term with $E = e_ie_j^{\mathsf T}$ and $E = e_ke_l^{\mathsf T}$ gives the mixed partials. Equivalently, in matrix calculus one differentiates $d\lambda = (w^{\mathsf T}\otimes v^{\mathsf T})\,d\operatorname{vec}A$ again, inserts the derivatives of the normalized eigenvectors, and reads off the Hessian from $d^2\lambda = d\operatorname{vec}A^{\mathsf T}\,B\,d\operatorname{vec}A$ (Magnus–Neudecker second identification theorem, $H = \tfrac12(B + B^{\mathsf T})$); this avoids computing all eigenvectors. With $\lambda$ as fitness, the pure second derivatives $\partial^2\lambda/\partial\theta^2$ are quadratic selection gradients: negative, zero and positive values mean concave, linear and convex selection on $\theta$, and at a singular strategy decide evolutionary stability versus branching; a negative or positive mixed derivative means selection to decrease or increase the correlation of two traits. Second derivatives also give sensitivities of Tuljapurkar's small-noise approximation of the stochastic growth rate. For the herb *Calathea ovandensis* the Hessian with respect to stage-specific survival shows negative correlational selection between seed or seedling survival and adult survival.

## Sources

- E. Shyu and H. Caswell, "Calculating second derivatives of population growth rates for ecology and evolution", Methods in Ecology and Evolution 5(5) (2014) 473–482, Eqs. (12)–(25), (26)–(38), (39)–(45), (46)–(58), <https://doi.org/10.1111/2041-210X.12179>, PMCID PMC4358155.
- H. Caswell, *Matrix Population Models*, 2nd ed., Sinauer (2001), Section 9.7 (second derivatives via all eigenvalues and eigenvectors).
