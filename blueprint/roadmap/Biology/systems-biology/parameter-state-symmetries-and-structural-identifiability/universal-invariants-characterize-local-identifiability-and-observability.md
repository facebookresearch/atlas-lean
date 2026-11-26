# Universal invariants characterize local identifiability and observability

**Setting.** A model $\dot{\mathbf x}=\mathbf f(t,\mathbf x,\boldsymbol\theta)$ with states $\mathbf x\in\mathbb R^n$, parameters $\boldsymbol\theta\in\mathbb R^p$ and observed outputs $\mathbf y(t,\mathbf x,\boldsymbol\theta)$. A parameter $\theta_\ell$ is locally structurally identifiable near $\boldsymbol\theta_C$ if, for $\boldsymbol\theta,\boldsymbol\theta^\star$ in a ball around $\boldsymbol\theta_C$ and all admissible states, $\mathbf y(t,\mathbf x,\boldsymbol\theta)=\mathbf y(t,\mathbf x,\boldsymbol\theta^\star)$ for all $t$ implies $\theta_\ell=\theta_\ell^\star$; local structural observability of a state $x_i$, and identifiability or observability of combinations $\phi(\boldsymbol\theta)$ or $\phi(\boldsymbol\theta,\mathbf x)$, are defined in the same way.

**Parameter-state symmetries.** A one-parameter family $(t,\mathbf x,\boldsymbol\theta)\mapsto(t,\hat{\mathbf x}(t,\mathbf x,\boldsymbol\theta,\varepsilon),\hat{\boldsymbol\theta}(\boldsymbol\theta,\varepsilon))$ with generator

$$X=\sum_{i=1}^n\eta_i(t,\mathbf x,\boldsymbol\theta)\,\partial_{x_i}+\sum_{\ell=1}^p\chi_\ell(\boldsymbol\theta)\,\partial_{\theta_\ell}$$

(no time infinitesimal, parameter infinitesimals depending on $\boldsymbol\theta$ only) is a parameter-state symmetry if it maps solutions to solutions, i.e. the first prolongation satisfies $X^{(1)}(\dot{\mathbf x}-\mathbf f)=\mathbf 0$ on solutions, and preserves the outputs, $X(\mathbf y)=\mathbf 0$. A function $I(t,\mathbf x,\dot{\mathbf x},\boldsymbol\theta)$ with $X^{(1)}(I)=0$ for every such generator is a universal invariant.

**Theorems.** (1) A parameter $\theta_\ell$ is locally structurally identifiable iff it is a universal parameter invariant; more generally, the locally identifiable parameter combinations are exactly the universal parameter invariants. (2) A state $x_i$ is locally structurally observable iff it is a universal state invariant, and the locally observable parameter-state combinations are exactly the universal parameter-state invariants.

## Expansion

If $\theta_\ell$ is identifiable, then along any symmetry orbit the outputs stay fixed, so $\hat\theta_\ell(\varepsilon)$ must be locally constant, and by analyticity constant: $\theta_\ell$ is invariant. Conversely, if $\theta_\ell$ is preserved by every output-preserving parameter-state symmetry, then no infinitesimal output-preserving transformation changes it, and local identifiability follows from the infinitesimal (linearized) output invariance conditions. Fixing time ($\xi=0$) is what makes output preservation hold pointwise in $t$, the requirement in the definitions. Computing generators reduces to solving the linear determining equations, applied in the paper to a glucose–insulin model and an SEI tuberculosis model.

## Sources

- J. G. Borgqvist, A. P. Browning, F. Ohlsson, R. E. Baker, "Framing local structural identifiability and observability in terms of parameter-state symmetries", arXiv:2603.11387 (2026), Definitions 1–11, Theorems 1 and 2, Corollaries 1 and 2, <https://doi.org/10.48550/arXiv.2603.11387>.
