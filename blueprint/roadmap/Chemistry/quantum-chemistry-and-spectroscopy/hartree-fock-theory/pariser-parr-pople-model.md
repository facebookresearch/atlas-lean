# Pariser–Parr–Pople model

The Pariser–Parr–Pople model is a semiempirical closed-shell self-consistent-field model for the π electrons of a conjugated molecule, with one orbital per atom, zero differential overlap and parametrized one- and two-centre integrals.

Fix $n$ sites (atoms contributing one π orbital each), an even number $2m\le2n$ of π electrons, and real parameters: valence-state potentials $U_r$, effective core charges $Z_s$, electron-repulsion integrals $\gamma_{rs}=\gamma_{sr}$ (including one-centre $\gamma_{rr}$) and resonance integrals $\beta_{rs}=\beta_{sr}$ for $r\ne s$. Under zero differential overlap the site basis is orthonormal ($S=\mathbf 1$). The core matrix is

$$
H_{rr}=\alpha_r=U_r-\sum_{s\ne r}Z_s\gamma_{rs},\qquad H_{rs}=\beta_{rs}\ (r\ne s),
$$

and for a real symmetric density matrix $P$ the Fock matrix is

$$
F_{rr}=H_{rr}+\sum_{t}P_{tt}\gamma_{rt}-\frac12P_{rr}\gamma_{rr},\qquad F_{rs}=H_{rs}-\frac12P_{rs}\gamma_{rs}\ (r\ne s),
$$

where the sum runs over all sites $t$, including $t=r$. The model's self-consistent-field equations are $F(P)C=C\varepsilon$ with $C$ a real orthogonal $n\times n$ matrix of spatial-orbital coefficients and $\varepsilon$ diagonal. Following the standard closed-shell restricted convention, which the source does not spell out, $P_{rs}=2\sum_{i=1}^{m}C_{ri}C_{si}$ with the $m$ doubly occupied columns chosen as those of the $m$ lowest eigenvalues (aufbau filling, a choice). Parameter formulas (for example $\gamma_{rr}$ from valence-state ionization energies and affinities) are empirical choices, not part of the model.

## Context

Graduate. Setting all $\gamma=0$ gives $F=H$, a Hückel-type matrix with Coulomb integrals $\alpha_r=U_r$ and resonance integrals $\beta_{rs}$ (compare the [Hückel matrix of a graph](../variational-method-perturbation-theory-and-h-cke/huckel-matrix.md)). Jorner, Pollice, Lavigne and Aspuru-Guzik combine this model with configuration interaction and perturbation theory for ultrafast screening of inverted singlet–triplet gap molecules. It is a spatial-orbital instance of the closed-shell Roothaan equations, with $n$ spatial basis functions and $m$ doubly occupied columns, not of the spin-orbital form.

## Depends on

None.

## Proof depends on

None.

## Expansion

A model definition. It arises from the closed-shell Roothaan Fock matrix by neglecting all differential overlap $\chi_r\chi_s$ ($r\ne s$) in the two-electron integrals, keeping only $(rr|ss)=\gamma_{rs}$, and replacing the remaining integrals by parameters; the $-\frac12P_{rr}\gamma_{rr}$ term removes half of the same-site Coulomb term, which is the exchange contribution.

## Sources

- Kjell Jorner, Robert Pollice, Cyrille Lavigne and Alán Aspuru-Guzik, *Ultrafast Computational Screening of Molecules with Inverted Singlet–Triplet Energy Gaps Using the Pariser–Parr–Pople Semiempirical Quantum Chemistry Method*, J. Phys. Chem. A 128 (2024) 2445–2456, <https://doi.org/10.1021/acs.jpca.3c06357> (PMC10983003), 'PPP Theory', Eqs. (1)–(5) (model) and Eqs. (6)–(12) (parametrization).
