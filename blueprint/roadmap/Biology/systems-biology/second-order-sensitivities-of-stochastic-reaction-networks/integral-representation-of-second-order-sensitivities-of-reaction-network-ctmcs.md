# Integral representation of second-order parameter sensitivities of stochastic reaction networks

**Setting.** A stochastic reaction network with $M$ reactions of stoichiometric vectors $\zeta_1, \dots, \zeta_M \in \mathbb{Z}^N$ and propensities $\lambda_k(x,\theta)$ is a continuous-time Markov chain $X_\theta(t)$ on $\mathbb{N}^N$ with generator $\mathbb{A}_\theta g(x) = \sum_k\lambda_k(x,\theta)\,\Delta_{\zeta_k}g(x)$, where $\Delta_\zeta g(x) = g(x+\zeta) - g(x)$. For an output $f$ let $\Psi_\theta(x,f,t) = \mathbb{E}_x[f(X_\theta(t))]$, and define the first- and second-order sensitivities
$$S^{(i)}_\theta(x,f,t) = \frac{\partial\Psi_\theta(x,f,t)}{\partial\theta_i}, \qquad S^{(i,j)}_\theta(x,f,t) = \frac{\partial^2\Psi_\theta(x,f,t)}{\partial\theta_i\,\partial\theta_j}.$$

**Theorem.** Assume the propensities satisfy growth and regularity conditions at $\theta$ allowing Dynkin's formula and twice differentiability in $(\theta_i, \theta_j)$, and that $f$ has polynomial growth. Then for every initial state $x_0$ and $T > 0$, $S^{(i,j)}_\theta(x_0,f,T)$ exists and equals $\mathbb{E}_{x_0}[s^{(i,j)}_\theta(f,T)]$ with
$$\begin{aligned}
s^{(i,j)}_\theta(f,T) = \sum_{k=1}^M\Bigg[&\int_0^T\frac{\partial^2\lambda_k}{\partial\theta_i\partial\theta_j}(X_\theta(s),\theta)\,\Delta_{\zeta_k}\Psi_\theta(X_\theta(s),f,T-s)\,ds\\
&+ \int_0^T\frac{\partial\lambda_k}{\partial\theta_i}(X_\theta(s),\theta)\,\Delta_{\zeta_k}S^{(j)}_\theta(X_\theta(s),f,T-s)\,ds + \int_0^T\frac{\partial\lambda_k}{\partial\theta_j}(X_\theta(s),\theta)\,\Delta_{\zeta_k}S^{(i)}_\theta(X_\theta(s),f,T-s)\,ds\Bigg].
\end{aligned}$$
Each term is an expectation along a single path of differences of conditional expectations (and first-order sensitivities) between the state and its neighbor after one reaction; estimating these differences with coupled auxiliary paths gives the unbiased *Double Bernoulli Path Algorithm*, an alternative to Girsanov (likelihood-ratio) estimators with typically much smaller variance.

## Depends on

- [Composition–multiplier closure of linear-rate ODE hierarchies](../linear-rate-closure-of-master-equation-hierarchies/composition-multiplier-closure-of-linear-rate-ode-hierarchies.md)

## Expansion

Differentiating the Kolmogorov backward equation $\partial_t\Psi = \mathbb{A}_\theta\Psi$ once in $\theta_j$ gives an inhomogeneous backward equation for $S^{(j)}$ with source $\partial_{\theta_j}\mathbb{A}_\theta\Psi$, whose Duhamel (Dynkin) representation is the first-order integral formula of Gupta and Khammash. Differentiating again in $\theta_i$ produces three sources: the second derivative of the generator applied to $\Psi$ and the two mixed terms $\partial_{\theta_i}\mathbb{A}_\theta S^{(j)}$, $\partial_{\theta_j}\mathbb{A}_\theta S^{(i)}$. Writing $\partial\mathbb{A}_\theta$ through $\partial\lambda_k\,\Delta_{\zeta_k}$ and applying Dynkin's formula along the chain yields the stated path integral; growth assumptions make all moments finite.

## Sources

- Q. Badolle, A. Gupta and M. Khammash, "Unbiased estimation of second-order parameter sensitivities for stochastic reaction networks", arXiv:2410.11471 (2024), Theorem 2.1, Section 3 and Lemma A.1, <https://doi.org/10.48550/arXiv.2410.11471>.
