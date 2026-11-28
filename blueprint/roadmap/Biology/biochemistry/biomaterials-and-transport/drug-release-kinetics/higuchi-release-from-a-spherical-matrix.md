# Higuchi release from a spherical matrix

For a sphere of radius $a$ with dispersed drug, Higuchi's pseudo-steady model relates the radius $R$ of the undissolved core to time and to the released fraction, with a separate high-loading reduction.

Under the planar Higuchi assumptions, in a sphere of radius $a$ with loading $A$, solubility $C_s$, $q = C_s/A \in (0,1)$, diffusivity $D > 0$ and a receding undissolved core of radius $R(t) \in (0, a)$, take the quasi-static profile

$$C(r,t) = C_s\,\frac{R\,(a - r)}{r\,(a - R)}, \qquad R < r < a .$$

Then the released fraction and the core radius satisfy

$$\frac{M_t}{M_\infty} = 1 - \left(\frac{R}{a}\right)^{3} + \frac{q}{2}\left[2\left(\frac{R}{a}\right)^{3} - \left(\frac{R}{a}\right)^{2} - \frac{R}{a}\right],$$

$$\frac{6C_sDt}{Aa^2} = 2\left(\frac{R}{a}\right)^{3} - 3\left(\frac{R}{a}\right)^{2} + 1 - q\left[2\left(\frac{R}{a}\right)^{3} - 4\left(\frac{R}{a}\right)^{2} + \frac{R}{a} + 1 + \ln\frac{R}{a}\right].$$

For $A \gg C_s$ the source reduces these to $M_t/M_\infty = 1 - (R/a)^3$ and $6C_sDt/(Aa^2) = 2(R/a)^3 - 3(R/a)^2 + 1$ (its Eqs. (33)–(34)).

## Context

Graduate. The spherical case shows how geometry changes the time course of Higuchi-type release. At $R = a$ both right-hand sides vanish, while the profile itself is defined only for $R < a$. The finite-loading and high-loading relations differ near exhaustion: by inspection of the displayed time relation, its term $-q\ln(R/a)$ grows without bound as $R \to 0$ when $q > 0$, so the core vanishes only as $t \to \infty$ in the finite-loading relation, whereas the reduced relation reaches $R = 0$ at $t^* = Aa^2/(6C_sD)$; the source does not discuss this limit.

## Depends on

- [Higuchi pseudo-steady-state release from a planar matrix](higuchi-pseudo-steady-state-release.md)

## Proof depends on

None.

## Expansion

Derivation route (one balance, not two): the profile is the steady radial solution of Laplace's equation with $C(R) = C_s$, $C(a) = 0$. Write the total drug remaining as undissolved core $\tfrac43\pi R^3 A$ plus dissolved drug in the shell computed from the profile, and set its rate of decrease equal to the outward flux at $r = a$, $4\pi D C_s aR/(a - R)$; integrate from $R = a$. Combining this storage balance with a separate front (Stefan) condition would double-count. The open copy's equations were extracted from images with flattened fractions, so each bracket must be re-derived.

## Sources

- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 3.1.3, Figure 8, Eqs. (30)–(32) for finite loading and Eqs. (33)–(34) for the $A \gg C_s$ reduction
