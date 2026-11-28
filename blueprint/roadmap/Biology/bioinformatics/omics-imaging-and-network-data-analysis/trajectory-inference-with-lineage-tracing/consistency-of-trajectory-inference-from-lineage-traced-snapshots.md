# Consistency of trajectory inference from lineage-traced snapshots

**Setting.** Snapshots are taken at times $0 \le t_1 < \dots < t_N = T$. At time $t_i$ one observes
$K_i$ independent lineage trees of a branching SDE with gradient drift $v = -\nabla\Psi$, diffusivity
$\tau$, birth rate $b$ and **zero death rate**, every leaf observed, with generation number
$m_{j,k,i}$ and gene expression $x_{j,k,i}$ for leaf $j$ of tree $k$. Form the reweighted empirical
probability measures

$$\hat p_{t_i} = \frac{1}{K_i}\sum_{k=1}^{K_i}\sum_{j=1}^{n_{k,i}} 2^{-m_{j,k,i}}\,\delta_{x_{j,k,i}} .$$

Let $W^\tau$ be the law of Brownian motion with diffusivity $\tau$, $H$ the relative entropy, $\Phi_h$ a
Gaussian kernel of width $h$, and

$$F_{N,\lambda,h}(R) = \tau H(R\,|\,W^\tau) + \frac{1}{\lambda}\sum_{i=1}^{N}(t_{i+1}-t_i)\,H\big(\Phi_h * \hat p_{t_i}\,\big|\,R_{t_i}\big)$$

the global Waddington-OT (gWOT) functional over path measures $R$ on $C([0,T],\mathcal X)$, with
$R_{t_i}$ the time marginals.

**Theorem 7.** Let $R_{N,\lambda,h}$ minimize $F_{N,\lambda,h}$. In the limit $N\to\infty$ (time points
becoming dense in $[0,T]$), followed by $\lambda\to0$ and $h\to0$, $R_{N,\lambda,h}$ converges narrowly to
the path measure $P^\tau$ of the underlying SDE $dX_t = -\nabla\Psi(t,X_t)\,dt + \sqrt\tau\,dB_t$. The
convergence does not depend on the number of trees or cells per time point, and no prior knowledge of
the division rate is needed.

## Depends on

- [Generation-structured master equation of a branching SDE](generation-structured-master-equation-of-a-branching-sde.md)

## Proof depends on

- [Generation reweighting removes proliferation from a branching SDE](generation-reweighting-removes-proliferation-from-a-branching-sde.md)

## Expansion

By the law of large numbers over time points, time-weighted averages of the smoothed empirical
generation-resolved measures converge to $\int_0^T\sum_m\int a(m,x)\,\Phi_h*\rho_t(m,dx)\,dt$; choosing
$a(m,x) = f(x)2^{-m}$ and using that the reweighted intensity equals the SDE law (zero death) shows that
the reweighted snapshots $\Phi_h*\hat p_{t_i}$ have exactly the temporal behaviour required by the
consistency theorem of gWOT for non-branching diffusions, which then applies verbatim. Without lineage
information the analogous unbalanced Schrödinger problem has a drift that depends on the assumed
branching rates of the reference process, so proliferation and differentiation cannot be
disentangled; generation numbers remove that ambiguity. Drift and birth rate can then be estimated
numerically, for example by mean-field Langevin methods.

## Sources

- E. Ventre, A. Forrow, N. Gadhiwala, P. Chakraborty, O. Angel, G. Schiebinger, "Trajectory inference for a branching SDE model of cell differentiation via lineage tracing", Journal of Mathematical Biology 92(5) (2026) 68, <https://doi.org/10.1007/s00285-026-02375-5> (PMC13090286). Introduction (mathematical overview, Eqs. 1–3, Theorem 1), Section 4.1, Theorem 7 (Eq. 15) and its proof, Eq. (16).
