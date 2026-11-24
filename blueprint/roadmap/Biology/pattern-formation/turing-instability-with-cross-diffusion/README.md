# Turing instability with cross-diffusion

Linear Turing theory for the system $w_t = D w_{xx} + J w$ with an arbitrary real $2 \times 2$
diffusion matrix $D$, which may be non-diagonal: the flux of one species can depend on the gradient
of the other. A Fourier mode is unstable when $J - k^2 D$ has an eigenvalue with positive real part,
and $\det(J - k^2 D) = h(k^2)$ for the dispersion polynomial $h(q) = \det D\, q^2 - b\, q + \det J$,
with $b = J_{00} D_{11} + J_{11} D_{00} - J_{01} D_{10} - J_{10} D_{01}$. For stable kinetics
($\operatorname{tr} J < 0 < \det J$), $\operatorname{tr} D \ge 0$ and $\det D > 0$, some mode is
unstable if and only if $2\sqrt{\det D \det J} < b$. Diagonal diffusion with nonnegative
coefficients cannot destabilize stable kinetics whose species are self-limiting ($f_u, g_v \le 0$),
but chemotactic cross-diffusion can: the archetype is Keller–Segel chemotaxis, with logistic growth
and in its minimal form. Instability here means linear (spectral) instability of the homogeneous
state.

## Definitions

- [Mode matrix J − k²D for a full diffusion matrix](cross-mode-matrix.md)
- [Linearly unstable Fourier mode with cross-diffusion](is-cross-unstable-mode.md)
- [Classical solution of the linearized cross-diffusion system](is-cross-linearized-solution.md)
- [Mixed coefficient b of the cross-diffusion dispersion polynomial](cross-coeff.md)
- [Cross-diffusion dispersion polynomial h(q) = det D q² − b q + det J](cross-dispersion-det.md)
- [Discriminant Δ = b² − 4 det D det J of the cross-diffusion band](cross-band-discriminant.md)
- [Lower end (b − √Δ)/(2 det D) of the cross-diffusion unstable band](cross-band-lower.md)
- [Upper end (b + √Δ)/(2 det D) of the cross-diffusion unstable band](cross-band-upper.md)

## The mode matrix and the dispersion relation

- [The trace of J − k²D is tr J − k² tr D](trace-cross-mode-matrix.md)
- [The determinant of J − k²D is the dispersion polynomial at k²](det-cross-mode-matrix.md)
- [A mode is unstable iff tr(J − k²D) > 0 or det(J − k²D) < 0](is-cross-unstable-mode-iff.md)
- [For diagonal diffusion, the mode matrix is the Turing mode matrix](cross-mode-matrix-diffusion-matrix.md)
- [For diagonal D, cross-diffusion instability is Turing instability](is-cross-unstable-mode-diffusion-matrix.md)
- [For diagonal diffusion, the mixed coefficient is d_v f_u + d_u g_v](cross-coeff-diffusion-matrix.md)
- [For diagonal diffusion, the dispersion polynomial is the Turing one](cross-dispersion-det-diffusion-matrix.md)
- [Dispersion relation with cross-diffusion](fourier-mode-is-cross-linearized-solutio.md)
- [A mode is unstable iff it carries a growing Fourier-mode solution](is-cross-unstable-mode-iff-exists-growin.md)

## Turing's criterion with cross-diffusion

- [For stable kinetics, the homogeneous mode is stable whatever D](not-is-cross-unstable-mode-zero.md)
- [For tr J < 0 and tr D ≥ 0, a mode is unstable iff h(k²) < 0](is-cross-unstable-mode-iff-cross-dispers.md)
- [Stable kinetics and det(J − k²D) < 0 give diffusion-driven instability](cross-turing-instability.md)
- [For det D, det J > 0, h(q) < 0 at some q ≥ 0 iff 2√(det D det J) < b](exists-cross-dispersion-det-neg-iff.md)
- [2√(det D det J) < b iff b > 0 and 4 det D det J < b²](two-mul-sqrt-lt-cross-coeff-iff.md)
- [Turing's criterion with cross-diffusion: 2√(det D det J) < b](exists-is-cross-unstable-mode-iff.md)
- [For det D > 0, h(q) < 0 for every q strictly inside the band (q₋, q₊)](cross-dispersion-det-neg-of-mem-band.md)
- [Under the cross-diffusion criterion, long intervals have unstable k_n](exists-is-cross-unstable-mode-neumann-wa.md)

## Self-limiting kinetics under diagonal diffusion

- [With f_u, g_v ≤ 0, no diagonal diffusion destabilizes stable kinetics](not-exists-is-unstable-mode-of-nonpos.md)

## Keller–Segel chemotaxis

- [Keller–Segel kinetics: logistic cells and a decaying chemoattractant](keller-segel-kinetics.md)
- [Homogeneous state (1, α/β) of the Keller–Segel kinetics](keller-segel-steady-state.md)
- [Keller–Segel Jacobian ((−r, 0), (α, −β)) at (1, α/β)](keller-segel-jacobian.md)
- [Linearized Keller–Segel diffusion matrix ((d_u, −χu₀), (0, d_v))](keller-segel-diffusion.md)
- [Keller–Segel flux (d_u u_x − χ u v_x, d_v v_x)](keller-segel-flux.md)
- [Linearization of the chemotactic flux](keller-segel-flux-add.md)
- [For β ≠ 0, (1, α/β) is a steady state of the Keller–Segel kinetics](keller-segel-steady-state-2.md)
- [The Keller–Segel kinetics have Jacobian ((−r, 0), (α, −β)) at (1, α/β)](jacobian-matrix-keller-segel.md)
- [For Keller–Segel, the mixed coefficient is b = αχu₀ − r d_v − β d_u](cross-coeff-keller-segel.md)
- [Without chemotaxis, the Keller–Segel diffusion matrix is diagonal](keller-segel-diffusion-zero.md)
- [For r, β, d_u, d_v > 0, chemotactic instability criterion at (1, α/β)](keller-segel-turing-iff.md)
- [Large χ destabilizes Keller–Segel, which no diagonal diffusion does](keller-segel-cross-diffusion-driven.md)

## The minimal Keller–Segel model

- [For β ≠ 0, every (u₀, αu₀/β) is a steady state of the minimal model](minimal-keller-segel-steady-state.md)
- [The minimal Keller–Segel kinetics have Jacobian ((0, 0), (α, −β))](jacobian-matrix-minimal-keller-segel.md)
- [Minimal Keller–Segel: h(k²) = k²(d_u d_v k² − (αχu₀ − βd_u))](cross-dispersion-det-minimal-keller-sege.md)
- [Minimal Keller–Segel: k ≠ 0 is unstable iff d_u d_v k² < αχu₀ − βd_u](minimal-keller-segel-is-cross-unstable-m.md)
- [For β > 0, the minimal Keller–Segel homogeneous mode is not unstable](minimal-keller-segel-not-is-cross-unstab.md)
- [Minimal Keller–Segel on an interval: some n ≥ 1 unstable iff n = 1 is](minimal-keller-segel-exists-neumann-iff.md)
