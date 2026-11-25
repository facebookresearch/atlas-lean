# For μ > 0, the deviatoric return satisfies maximum plastic work

Let $\mu > 0$, let $\mathcal K$ be a nonempty convex set of real $3 \times 3$ matrices that is
complete for the Frobenius distance (equivalently, closed) and consists of
[deviatoric stresses](deviatoric-stresses.md), and let $\sigma_{\mathrm{trial}}$ be a real
$3 \times 3$ matrix, not necessarily symmetric. With
$\sigma_m = \operatorname{tr} \sigma_{\mathrm{trial}} / 3$ its
[mean stress](../cauchy-stress-small-strain-and-mohr-s-circle/mean-stress.md), let
$\sigma = \sigma_m I + P_{\mathcal K}(s_{\mathrm{trial}})$ be the stress returned from the
[deviator](../cauchy-stress-small-strain-and-mohr-s-circle/deviatoric-stress.md)
$s_{\mathrm{trial}}$ by the
[nearest-point projection](../../../Analysis/hilbert-spaces/hilbert-projection-theorem/convex-projection.md)
and $\Delta\varepsilon_p = (\sigma_{\mathrm{trial}} - \sigma) / (2\mu)$ the
[plastic strain increment](plastic-strain-increment.md). Then for every $\tau \in \mathcal K$,

$$
(\sigma - \tau) : \Delta\varepsilon_p =
\sum_{i, j} (\sigma - \tau)_{ij}\, (\Delta\varepsilon_p)_{ij} \ge 0.
$$

So the returned stress does at least as much plastic work on $\Delta\varepsilon_p$ as every
admissible stress $\tau$, although $\sigma$ itself need not lie in $\mathcal K$, since it carries
the trial mean stress. The mean-stress part of $\sigma$ does no work on $\Delta\varepsilon_p$, which
is trace-free because $\mathcal K$ consists of trace-free matrices.
