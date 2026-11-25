# Mixed-precision iterative refinement: error recursion and limiting accuracy

Let $A$ be nonsingular, $x^* = A^{-1}b$, and fix a vector norm with its induced matrix norm. Consider iterates
$x_{i+1} = x_i + \hat d_i + g_i$, where the exact residual is $r_i = b - Ax_i$, the computed residual $\hat r_i$ satisfies
$\lVert \hat r_i - r_i \rVert \le \rho$, the computed correction satisfies $\lVert \hat d_i - A^{-1}\hat r_i \rVert \le \phi \lVert A^{-1} \hat r_i \rVert$
with $\phi < 1$, and the update rounding satisfies $\lVert g_i \rVert \le \gamma$. Then the errors $e_i = x_i - x^*$ satisfy
$\lVert e_{i+1} \rVert \le \phi \lVert e_i \rVert + (1 + \phi)\lVert A^{-1} \rVert \rho + \gamma$, hence
$\limsup_i \lVert e_i \rVert \le ((1 + \phi)\lVert A^{-1} \rVert \rho + \gamma)/(1 - \phi)$, approached geometrically; the iterates need not
converge to a single point. Carson and Higham prove the corresponding componentwise recursion and limiting accuracy for iterative
refinement with LU factorization in one precision, residuals in another and the working precision, as a separate page.

## Proof

It follows from $A^{-1}\hat r_i = -e_i + A^{-1}(\hat r_i - r_i)$ and
$e_{i+1} = A^{-1}(\hat r_i - r_i) + (\hat d_i - A^{-1}\hat r_i) + g_i$.

## Related topics

- [Forward error, backward error and conditioning interface](forward-error-backward-error-and-conditioning-interface.md)
- [The relative error bound](../floating-point-rounding/abs-fl-sub-le.md)

## Sources

- Accelerating the Solution of Linear Systems by Iterative Refinement in Three Precisions — E. Carson, N. J. Higham, MIMS EPrint 2017.24, University of Manchester, Sec. 3, Theorem 3.2 and Corollary 3.3. <https://eprints.maths.manchester.ac.uk/2562/1/paper.pdf>
