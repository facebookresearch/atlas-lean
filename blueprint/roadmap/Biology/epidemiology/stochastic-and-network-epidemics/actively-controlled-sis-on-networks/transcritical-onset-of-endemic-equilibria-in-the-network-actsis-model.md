# Transcritical onset of endemic equilibria in the network actively controlled SIS model

**Model (network actSIS).** Consider $N$ populations indexed by $\mathcal{V} = \{1,\dots,N\}$. Population $j$ has infected fraction $p_j \in [0,1]$ and perceived infection level $p_{sj} \in [0,1]$. Infection spreads over a *contact graph* with symmetric $0/1$ adjacency matrix $A = (a_{jk})$, and risk perception spreads over a *communication graph* with adjacency matrix $\hat A = (\hat a_{jk})$ and in-degrees $\hat d_j = \sum_k \hat a_{jk} > 0$. With intrinsic transmission rate $\bar\beta > 0$, recovery rates $\delta_j > 0$, a perception time constant $\tau_s > 0$ and contact-response functions $\alpha_j : [0,1] \to [0,1]$ that are $C^1$ with $\alpha_j(0) \ne 0$,

$$
\dot p_j = (1-p_j)\,\bar\beta\,\alpha_j(p_{sj}) \sum_{k=1}^N a_{jk} p_k - \delta_j p_j, \qquad
\tau_s \dot p_{sj} = -p_{sj} + \frac{1}{\hat d_j}\sum_{k=1}^N \hat a_{jk} p_k .
$$

With $N = 1$ and $\hat A = A = (1)$ this is the well-mixed actSIS model $\dot p = \bar\beta\alpha(p_s)(1-p)p - \delta p$, $\tau_s \dot p_s = -p_s + p$; with $\alpha_j \equiv 1$ the first equation is the network SIS model.

**Statement.**

1. *Well-posedness.* The cube $[0,1]^{2N}$ is forward invariant.
2. *Threshold.* Assume $A$ and $\hat A$ irreducible, and let $D = \operatorname{diag}(\delta_1,\dots,\delta_N)$, $\tilde A = \operatorname{diag}(\alpha_1(0),\dots,\alpha_N(0))\,A$ and

$$
\bar\beta^* = \frac{1}{\rho(\tilde A D^{-1})}.
$$

The infection-free equilibrium $(\mathbf 0, \mathbf 0)$ is locally exponentially stable for $\bar\beta < \bar\beta^*$ and unstable for $\bar\beta > \bar\beta^*$.
3. *Bifurcation.* Let $\mathbf v^* \succ \mathbf 0$ and $\mathbf w^* \succ \mathbf 0$ be right and left null vectors of the irreducible Metzler matrix $-D + \bar\beta^* \tilde A$, and

$$
K_1 = \sum_{i=1}^N w_i^* \Bigl( (\hat\Delta^{-1}\hat A \mathbf v^*)_i\, \alpha_i'(0)\, (A\mathbf v^*)_i - 2 v_i^*\, \alpha_i(0)\, (A \mathbf v^*)_i \Bigr), \qquad \hat\Delta = \operatorname{diag}(\hat d_1,\dots,\hat d_N).
$$

If $K_1 \ne 0$, a branch of endemic equilibria $\mathbf p^* \succ \mathbf 0$, $\mathbf p_s^* = \hat\Delta^{-1}\hat A\mathbf p^*$ emerges from $(\mathbf 0,\mathbf 0)$ at $\bar\beta = \bar\beta^*$ in a transcritical bifurcation, along a center manifold tangent to $(\mathbf v^*, \hat\Delta^{-1}\hat A \mathbf v^*)$. If $K_1 < 0$ the branch exists for $\bar\beta > \bar\beta^*$ and is locally exponentially stable.
4. *Special cases.* If $\alpha_j'(0) \le 0$ for all $j$ (no population increases contacts as perceived risk first rises), then $K_1 < 0$, so a locally exponentially stable endemic branch appears for $\bar\beta > \bar\beta^*$. If moreover $\delta_j = \delta$ and $\alpha_j(0) = 1$ for all $j$, then $\bar\beta^* = \delta/\lambda_{\max}(A)$ and $\mathbf v^*$ is the Perron–Frobenius eigenvector of $A$.

In particular the communication graph $\hat A$ does not affect the epidemic threshold; it enters only the curvature coefficient $K_1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Threshold theorem for the SIS model](../../sis-epidemic-model/deriv-infected-pos-iff.md)

## Proof sketch

Invariance follows from Nagumo's theorem: on each face of the cube the vector field points inward ($p_j = 0 \Rightarrow \dot p_j \ge 0$, $p_j = 1 \Rightarrow \dot p_j = -\delta_j < 0$, and similarly for $p_{sj}$). At the origin the Jacobian is block lower triangular, with blocks $-D + \bar\beta \tilde A$ and $-\tau_s^{-1} I$. The first block is irreducible Metzler, so by Perron–Frobenius its leading eigenvalue is real, simple, has a positive eigenvector, and is negative exactly when $\bar\beta\,\rho(\tilde A D^{-1}) < 1$; this gives the threshold. At $\bar\beta = \bar\beta^*$ a simple zero eigenvalue appears, and a second-order Lyapunov–Schmidt reduction along it reads

$$
h(x,\bar\beta) = K_0\, x\,(\bar\beta - \bar\beta^*) + \bar\beta^* K_1 x^2 + \text{h.o.t.}, \qquad K_0 = \langle \mathbf w^*, \tilde A \mathbf v^* \rangle > 0 .
$$

The recognition conditions for a transcritical point ($h = h_x = h_\beta = 0$, $h_{xx} \ne 0$, $\det d^2 h = -K_0^2 < 0$) hold when $K_1 \ne 0$, and the sign of $K_1$ fixes the side and stability of the branch. When $\alpha_i'(0) \le 0$ both terms in $K_1$ are nonpositive and the second is strictly negative since $\mathbf v^*, \mathbf w^* \succ \mathbf 0$ and $A$ is irreducible.

## Sources

- Anastasia Bizyaeva, Marcela Ordorica Arango, Yunxiu Zhou, Simon Levin and Naomi Ehrich Leonard, "Active Risk Aversion in SIS Epidemics on Networks", in *2024 American Control Conference (ACC)*, IEEE, 2024, 4428–4433, <https://doi.org/10.23919/acc60939.2024.10644997>. Preprint version: arXiv:2311.02204 (2023), Theorem IV.1, Theorem IV.2 and Corollary IV.1, <https://doi.org/10.48550/arXiv.2311.02204>.
