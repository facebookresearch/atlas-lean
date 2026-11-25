# Deviatoric return map for perfect plasticity

Let $\mu > 0$ be the shear modulus, let the yield section $\mathcal K$ be a nonempty convex set of
real $3 \times 3$ matrices that is complete for the Frobenius distance (equivalently, closed) and
consists of [deviatoric stresses](deviatoric-stresses.md), and let $\sigma_{\mathrm{trial}}$ be a
[symmetric](../cauchy-stress-small-strain-and-mohr-s-circle/is-symmetric-stress.md) real
$3 \times 3$ matrix. Write $\sigma_m = \operatorname{tr} \sigma_{\mathrm{trial}} / 3$ for its
[mean stress](../cauchy-stress-small-strain-and-mohr-s-circle/mean-stress.md) and
$s_{\mathrm{trial}} = \sigma_{\mathrm{trial}} - \sigma_m I$ for its
[deviator](../cauchy-stress-small-strain-and-mohr-s-circle/deviatoric-stress.md), let
$s = P_{\mathcal K}(s_{\mathrm{trial}})$ be the
[nearest-point projection](../../../Analysis/hilbert-spaces/hilbert-projection-theorem/convex-projection.md)
of $s_{\mathrm{trial}}$ onto $\mathcal K$ in the [Frobenius norm](frobenius-inner-eq-sum-mul.md),
and let $\sigma = \sigma_m I + s$ be the returned stress and
$\Delta\varepsilon_p = (\sigma_{\mathrm{trial}} - \sigma) / (2\mu)$ the
[plastic strain increment](plastic-strain-increment.md). Then:

- $s_{\mathrm{trial}}$ is symmetric and trace-free, and $s \in \mathcal K$;
- $\sigma$ is symmetric, its mean stress is $\sigma_m$ and its deviator is $s$;
- $\Delta\varepsilon_p = (s_{\mathrm{trial}} - s) / (2\mu)$, and $\Delta\varepsilon_p$ is symmetric
  and trace-free: there is no volumetric plastic strain;
- $\sigma = \sigma_{\mathrm{trial}} - 2\mu\, \Delta\varepsilon_p$;
- if $s_{\mathrm{trial}} \in \mathcal K$, then $\Delta\varepsilon_p = 0$ and
  $\sigma = \sigma_{\mathrm{trial}}$.

The model is perfect plasticity: there is no hardening, and the stresses are tension positive.
