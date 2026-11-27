# Constant dosing is optimal for positive bilinear therapy models

**Model.** Let $x\in\mathbb R^n$ be the populations of $n$ virus mutants and $u\in\mathbb R^m$ the doses of $m$ drugs, with

$$\dot x = \big(A + D(u)\big)x + Bd, \qquad z = \begin{pmatrix}Q^{1/2}x\\ R^{1/2}u\end{pmatrix},$$

where $A$ is Metzler (off-diagonal entries $\ge0$: mutation; diagonal: net replication), $D(u) = \mathrm{diag}(D_uu) = \sum_kD_ku_k$ is diagonal and linear in $u$ (drug $k$ changes the death rate of each mutant), $B$ and $Q\succeq0$ have nonnegative entries, $R\succ0$, and $d$ is an exogenous disturbance. Signals live in the Besicovitch space $\mathcal B_2$ of bounded-power signals (including periodic and almost periodic ones), with power norm $\|v\|^2_{\mathrm{pow}} = \limsup_{T\to\infty}\frac1T\int_0^T|v|^2$. Assume a constant stabilizing dose $\bar u$ exists. The performance is the worst-case power gain

$$J(u) = \sup_{\|d\|_{\mathrm{pow}}\le1}\ \|z_{u,d}\|^2_{\mathrm{pow}}.$$

**Theorem.**

1. (Constant optimal control.) The problem of minimizing $J(u)$ over stabilizing bounded $u\in\mathcal B_2$ is solved by a constant input $u(t)\equiv u^\star$.
2. (Convex reduction.) For constant $\bar u$ with $A_{\mathrm{cl}} = A + D(\bar u)$ Hurwitz, the worst disturbance is constant and

$$J(\bar u) = \bar\sigma_{\mathrm{cl}}^2 + \bar u^{T}R\bar u, \qquad \bar\sigma_{\mathrm{cl}} = \sigma_{\max}\big(-Q^{1/2}A_{\mathrm{cl}}^{-1}B\big),$$

a convex, non-smooth function of $\bar u$, with subdifferential

$$\partial J(\bar u) = \Big\{2\bar\sigma_{\mathrm{cl}}\sum_i\alpha_iD_u^{T}\,\mathrm{diag}\big(A_{\mathrm{cl}}^{-1}Bv_iw_i^{T}Q^{1/2}A_{\mathrm{cl}}^{-1}\big) + 2R\bar u\Big\},$$

over unit pairs $(w_i,v_i)$ attaining the top singular value and convex weights $\alpha$, so $u^\star$ can be computed by a subgradient method.
3. (Robust design.) If $-D(u)$ has nonnegative diagonal for $u\ge0$ and the entries of $A$ and of the drug efficacies are uncertain within element-wise bounds, then, provided $(A + \tilde A - D(\beta)) + D(\bar u)$ is Hurwitz for some $\bar u$ (with $\tilde A$ and $\beta$ the element-wise uncertainty bounds), the minimax problem $\min_u\max_{\Delta}J(u;\Delta)$ is solved by the nominal problem for the worst-case system matrix $A + \tilde A - D(\beta)$, so robust dosing is no harder than nominal dosing.

## Expansion

For a positive system each state component is a convex function of the input, and $x^{T}Qx$ is nondecreasing in each component when $Q$ has nonnegative entries, so $\|z_{u,\bar d}\|^2_{\mathrm{pow}}$ is convex in $u$ for constant $\bar d$. Its directional derivative at a constant stabilizing $\bar u$ vanishes along every zero-mean variation $\tilde u$, so among inputs with the same mean the constant one minimizes; since the worst disturbance for constant inputs is constant, $J(u)\ge\|z_{u,\bar d}\|^2\ge J(\bar u)$ for the optimal constant $\bar u$. For constant data the steady state is $x = -A_{\mathrm{cl}}^{-1}B\bar d$, giving the singular-value formula, and positivity makes $-A_{\mathrm{cl}}^{-1}$ entrywise nonnegative and monotone in the data, which yields the worst-case reduction of item 3.

## Sources

- Neil K. Dhingra, Marcello Colombino, Mihailo R. Jovanović, Anders Rantzer, "On the optimal control problem for a class of monotone bilinear systems", arXiv (2016). Section 2 (problem formulation, Assumption 1), Section 3 (Lemmas 1–2, Theorem 3, Proposition 4), Section 4 (Theorem 5), Section 5 (combination drug therapy for HIV). <https://doi.org/10.48550/arXiv.1611.09984>. Published version: Marcello Colombino, Neil K. Dhingra, Mihailo R. Jovanović, Anders Rantzer, Roy S. Smith, Proceedings of the 22nd International Symposium on Mathematical Theory of Networks and Systems (MTNS 2016), Minneapolis, 411–413 (no DOI), <http://neilkdh.com/pub/coldhijovransmiMTNS2016.pdf>, where the results are Theorem 1, Proposition 2 and Theorem 3; locators above refer to the arXiv version.
