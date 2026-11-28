# Multiscale sloppiness and its characterization of structural identifiability

A model $M$ with parameter space $P\subseteq\mathbb R^r$ has a *model prediction map* $\phi:P\to\mathbb R^N$ giving the noise-free data at each parameter. Parameters are equivalent, $p\sim_{M,\phi}p'$, when $\phi(p)=\phi(p')$. The model is globally identifiable if $\phi$ is injective, generically identifiable if $\phi$ is generically injective, and locally identifiable if almost all nonempty fibres of $\phi$ have no accumulation points. It is rationally identifiable if each parameter is a rational function of the $\phi_i$, that is $\mathbb R(p_1,\dots,p_r)=\mathbb R(\phi_1,\dots,\phi_N)$.

A noise model $\psi$ for the observed data induces a premetric $d$ on $P$ through the Kullback–Leibler divergence between the data distributions at two parameters. The model is *sloppy* at $p_0$ when $d$ departs strongly from a chosen reference metric $d_P$ near $p_0$. The classical version, *infinitesimal sloppiness*, is the condition number of the Fisher information matrix at $p_0$. The *$\delta$-sloppiness* at $p_0$ is

$$
\mathcal S_{p_0}(\delta)=\frac{\sup\{d(p,p_0):d_P(p,p_0)=\delta\}}{\inf\{d(p,p_0):d_P(p,p_0)=\delta\}}.
$$

**Theorem.** If $P$ is closed in $\mathbb R^r$ and $d_P$ is strongly equivalent to the Euclidean metric (so every $d_P$-sphere in $P$ is compact), the equivalence class of $p_0$ is a single point if and only if

$$
\inf_{p\in P}\{d(p,p_0):d_P(p,p_0)=\delta\}>0\qquad\text{for all }\delta>0.
$$

In other words, finite $\delta$-sloppiness at every scale is equivalent to structural identifiability at $p_0$.

**Linear Gaussian case.** For additive Gaussian noise $\mathcal N(\phi(p),\Sigma)$ and linear $\phi$, the Fisher-information approximation is exact: $d_{\mathrm{FIM},p_0}=d$ for every $p_0$. If $\phi$ and $\psi$ are real-analytic and maximum likelihood estimates exist for generic data, then for almost all data the set of maximum likelihood estimates is exactly one $\sim_{M,\phi}$ equivalence class.

## Proof sketch

If $p\neq p_0$ has the same predictions, then $d(p,p_0)=0$ at scale $\delta=d_P(p,p_0)$, so the infimum vanishes. Conversely, a zero infimum at some scale gives, by compactness of the $d_P$-sphere and continuity, a distinct parameter with identical data distribution, hence identical predictions. Closedness of $P$ is needed for that compactness: on the open half-plane $P = \{x > 0\} \subset \mathbb R^2$ with $p_0 = (1,0)$, the map $\phi(x,y) = \big(1 - x(1-x),\ x(x-1)(x-\tfrac12),\ xy\big)$ is injective, yet $\phi(p) \to \phi(p_0)$ as $p \to (0,\sqrt3)$ along the circle $|p - p_0| = 2$, so the infimum at $\delta = 2$ is $0$. For linear Gaussian models the KL divergence is exactly the quadratic form $\tfrac12(p-p_0)^\top J^\top\Sigma^{-1}J(p-p_0)$, which is the Fisher metric. These notions apply to the ODE models of systems biology, where $\phi$ maps rate constants to observed trajectories.

## Sources

- Emilie Dufresne, Heather A. Harrington and Dhruva V. Raman, "The geometry of Sloppiness", *Journal of Algebraic Statistics* 9 (2018), 30–68, <https://doi.org/10.18409/jas.v9i1.64>. Preprint version: arXiv:1608.05679 (2016), Definitions 2.8, 3.1, 3.7, 4.2, 4.5, 4.11, Propositions 3.4, 4.9, 4.15 and Theorem 4.13, <https://doi.org/10.48550/arXiv.1608.05679>.
