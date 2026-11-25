# Deviatoric return map

In the space of symmetric trace-free stress tensors with the Frobenius inner product, let the yield set $K$ be nonempty, closed and
convex, fixed (no hardening) and independent of pressure. For isotropic elasticity with shear modulus $\mu > 0$, the associative return of a
trial stress $\sigma_{\mathrm{tr}}$ is its metric projection $\sigma = P_K(\sigma_{\mathrm{tr}})$, which exists and is unique, and the
plastic strain increment is $\Delta\varepsilon_p = (\sigma_{\mathrm{tr}} - \sigma)/(2\mu)$, which is zero exactly when
$\sigma_{\mathrm{tr}} \in K$. Closedness is needed: an open ball has no nearest point to a trial stress outside it. For a self-adjoint positive definite elastic operator $C$ mapping this same stress space to itself, the projection is instead taken in
the compliance inner product $\langle a,b\rangle_{C^{-1}}=\langle a,C^{-1}b\rangle_F$, and
$\Delta\varepsilon_p=C^{-1}(\sigma_{\mathrm{tr}}-\sigma)$. A full elastic operator coupling volumetric and deviatoric stresses requires
a different state space. Pressure-dependent yield surfaces and contact cones are not cases of the shear formula. Hardening, volumetric
plastic strain and a general anisotropic plasticity algorithm are outside this result.

## Depends on

## Proof depends on

## Expansion

Link a page for the metric projection onto a nonempty closed convex set in a finite-dimensional inner-product space, and check the
return-map statement against a computational plasticity source.

## Sources

- J. C. Simo and T. J. R. Hughes, *Computational Inelasticity*, Springer, 1998, Chapters 2–3 (return mapping).
