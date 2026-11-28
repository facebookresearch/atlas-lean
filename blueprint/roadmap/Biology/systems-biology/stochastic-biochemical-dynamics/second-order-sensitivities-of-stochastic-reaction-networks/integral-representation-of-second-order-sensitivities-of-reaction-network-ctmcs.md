# Integral representation of second-order parameter sensitivities of stochastic reaction networks

**Setting.** A stochastic reaction network with $M$ reactions of stoichiometric vectors $\zeta_1, \dots, \zeta_M \in \mathbb{Z}^N$ and propensities $\lambda_k(x,\theta)$ is a continuous-time Markov chain $X_\theta(t)$ on $\mathbb{N}^N$ with generator $\mathbb{A}_\theta g(x) = \sum_k\lambda_k(x,\theta)\,\Delta_{\zeta_k}g(x)$, where $\Delta_\zeta g(x) = g(x+\zeta) - g(x)$. For an output $f$ let $\Psi_\theta(x,f,t) = \mathbb{E}_x[f(X_\theta(t))]$, and define the first- and second-order sensitivities

$$S^{(i)}_\theta(x,f,t) = \frac{\partial\Psi_\theta(x,f,t)}{\partial\theta_i}, \qquad S^{(i,j)}_\theta(x,f,t) = \frac{\partial^2\Psi_\theta(x,f,t)}{\partial\theta_i\,\partial\theta_j}.$$

A function $g$ on $\mathbb N^n$ has *polynomial growth* if $|g(x)|\le C(1+|x|^r)$ for some $C,r\ge0$ and all $x$.

**Theorem.** Assume, at the parameter value $\theta\in\mathbb R^d$ and for the index pair $(i,j)$:
1. (stoichiometric admissibility) $\lambda_k(x,\theta)>0$ implies $x+\zeta_k\ge0$, for all $k$ and $x\in\mathbb N^N$;
2. (linear growth of net-producing reactions) there is $C_\lambda>0$ with $\sum_{k\in P}\lambda_k(x,\theta)\le C_\lambda(1+|x|)$ for all $x$, where $P=\{k:\sum_n\zeta_{k,n}>0\}$;
3. (regularity in $\theta$) for all $k$ and $x$, $\lambda_k(x,\cdot)$ is of class $C^3$ on $\mathbb R^d$ and $\partial^2_{\theta_i\theta_j}\lambda_k(x,\cdot)$ has polynomial growth, and for each $k$ there is $\epsilon>0$ such that $x\mapsto\sup_{\xi\in(\theta-\epsilon,\theta+\epsilon)}\max\{|\partial^3_{\theta_i\theta_i\theta_j}\lambda_k(x,\xi)|,|\partial^3_{\theta_i\theta_j\theta_j}\lambda_k(x,\xi)|\}$ has polynomial growth;
4. the output $f:\mathbb N^N\to\mathbb R$ has polynomial growth.

Then for every initial state $x_0$ and $T > 0$, $S^{(i,j)}_\theta(x_0,f,T)$ exists and equals $\mathbb{E}_{x_0}[s^{(i,j)}_\theta(f,T)]$ with

$$\begin{aligned}
s^{(i,j)}_\theta(f,T) = \sum_{k=1}^M\Bigg[&\int_0^T\frac{\partial^2\lambda_k}{\partial\theta_i\partial\theta_j}(X_\theta(s),\theta)\,\Delta_{\zeta_k}\Psi_\theta(X_\theta(s),f,T-s)\,ds\\
&+ \int_0^T\frac{\partial\lambda_k}{\partial\theta_i}(X_\theta(s),\theta)\,\Delta_{\zeta_k}S^{(j)}_\theta(X_\theta(s),f,T-s)\,ds + \int_0^T\frac{\partial\lambda_k}{\partial\theta_j}(X_\theta(s),\theta)\,\Delta_{\zeta_k}S^{(i)}_\theta(X_\theta(s),f,T-s)\,ds\Bigg].
\end{aligned}$$

Each term is an expectation along a single path of differences of conditional expectations (and first-order sensitivities) between the state and its neighbor after one reaction; estimating these differences with coupled auxiliary paths gives the unbiased *Double Bernoulli Path Algorithm*, an alternative to Girsanov (likelihood-ratio) estimators with typically much smaller variance.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)

## Expansion

Differentiating the Kolmogorov backward equation $\partial_t\Psi = \mathbb{A}_\theta\Psi$ once in $\theta_j$ gives an inhomogeneous backward equation for $S^{(j)}$ with source $\partial_{\theta_j}\mathbb{A}_\theta\Psi$, whose Duhamel (Dynkin) representation is the first-order integral formula of Gupta and Khammash. Differentiating again in $\theta_i$ produces three sources: the second derivative of the generator applied to $\Psi$ and the two mixed terms $\partial_{\theta_i}\mathbb{A}_\theta S^{(j)}$, $\partial_{\theta_j}\mathbb{A}_\theta S^{(i)}$. Writing $\partial\mathbb{A}_\theta$ through $\partial\lambda_k\,\Delta_{\zeta_k}$ and applying Dynkin's formula along the chain yields the stated path integral; growth assumptions make all moments finite.

## Sources

- Q. Badolle, A. Gupta and M. Khammash, "Unbiased estimation of second-order parameter sensitivities for stochastic reaction networks", *SIAM Journal on Scientific Computing* 48(1) (2026), A160–A184, Theorem 2.1, Section 3 and Lemma A.1, <https://doi.org/10.1137/24m1710097> (preprint arXiv:2410.11471).
