# Parameter-free rejection of ODE models via differential invariants and an augmented singular value test

**Setting.** A polynomial or rational ODE model with inputs $\mathbf{u}$, measured outputs $\mathbf{y}$, hidden states and unknown parameters $\mathbf{p}$ is reduced by differential elimination (Ritt pseudodivision, Rosenfeld–Gröbner or differential Gröbner bases) to input–output relations, *differential invariants*, of the form

$$\sum_{i=1}^n c_i(\mathbf{p})\,\psi_i(\mathbf{u}, \mathbf{y}) = \xi(\mathbf{u}, \mathbf{y}),$$

where the $\psi_i$ and $\xi$ are differential monomials/polynomials in $\mathbf{u}, \dot{\mathbf{u}}, \dots, \mathbf{y}, \dot{\mathbf{y}}, \dots$ and the $c_i$ are rational in $\mathbf{p}$, normalised so one coefficient is $1$. Evaluating at times $t_1, \dots, t_m$ ($m > n$) gives a linear system $A\kappa = b$ with $A_{ji} = \psi_i(\mathbf{u}(t_j), \mathbf{y}(t_j))$, $b_j = \xi(\mathbf{u}(t_j), \mathbf{y}(t_j))$ and unknown $\kappa = (c_i(\mathbf{p}))_i$; several invariants give a block-diagonal system. If the model generated the data, the system is solvable for some $\kappa$, whatever the parameter values.

**Theorem (augmented-matrix test).** Let $\tilde A, \tilde b$ be the matrices computed from noisy data (derivatives estimated, e.g., by Gaussian process regression). Under the null hypothesis $b \in \mathrm{range}(A)$,

$$\sigma_{n+1}\big([\tilde A, \tilde b]\big) \le \big\|[\tilde A - A,\ \tilde b - b]\big\| \le \|\tilde A - A\| + \|\tilde b - b\|,$$

where $\sigma_{n+1}$ is the $(n+1)$-st singular value. If the left side exceeds the right side, the model is rejected without estimating any parameter.

**Theorem (Gaussian tail bound).** If $C \in \mathbb{R}^{m \times n}$ is fixed and $Z$ has i.i.d. $N(0,1)$ entries, then for all $x \ge 0$

$$\Pr\big(\|C \circ Z\| \ge x\big) \le (m+n)\exp\Big(-\frac{x^2}{2\sigma^2}\Big), \qquad \sigma^2 = \max\Big(\max_i\|C_{i,:}\|^2,\ \max_j\|C_{:,j}\|^2\Big).$$

With multiplicative measurement noise $\tilde x = (1 + \epsilon Z)\circ x$, to first order $\tilde A - A = \epsilon\,C_{\tilde A}\circ Z$ with $(C_{\tilde A})_{ij} = \|\nabla\phi_{ij}(\tilde x)\circ\tilde x\|$ (and likewise for $b$), which turns the singular value test into a computable $p$-value bound for $\tau = \sigma_{n+1}([\tilde A, \tilde b])$.

## Proof sketch

Solvability means $\mathrm{rank}[A, b] = \mathrm{rank}\,A \le n$, so $\sigma_{n+1}([A, b]) = 0$, and Weyl's inequality $|\sigma_k(X) - \sigma_k(Y)| \le \|X - Y\|$ transfers this to the observed matrix up to the perturbation size. The Hadamard-product bound is a matrix Bernstein-type inequality for Gaussian series, and combining the two noise terms by convolution yields $\Pr(\tau \ge x) \le P_1(x) + P_2(x)$ with explicit Gaussian-integral expressions. The test can only reject: it may fail to reject when $A$ is numerically rank-deficient, and is uninformative when $m \le n$. Applied to time courses, it discriminates between competing mechanisms (e.g., alternative kinetic or signalling schemes) using only the structure of their invariants.

## Sources

- Heather A. Harrington, Kenneth L. Ho and Nicolette Meshkat, "A Parameter-Free Model Comparison Test Using Differential Algebra", *Complexity* 2019 (2019), 6041981, <https://doi.org/10.1155/2019/6041981>. Preprint version: arXiv:1603.09730 (2016), Section 2.4 (model rejection using differential invariants), Section 3.2 (augmented matrix theorem) and Section 4 (noise model and Hadamard tail bounds), <https://doi.org/10.48550/arXiv.1603.09730>.
