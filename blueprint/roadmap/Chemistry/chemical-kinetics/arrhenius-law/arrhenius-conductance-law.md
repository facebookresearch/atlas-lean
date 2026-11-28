# Arrhenius conductance law

The Arrhenius conductance model stipulates $G(T) = G_0\exp(-E_a/k_BT)$ on a temperature window; then $\ln(G/G_0)$ is affine in $1/T$ with slope $-E_a/k_B$.

On a stated temperature window $T \in [T_1, T_2]$ with $T_1 > 0$, the Arrhenius conductance model for a sample is

$$
G(T) = G_0\exp\!\left(-\frac{E_a}{k_BT}\right),
$$

with a constant prefactor $G_0 > 0$ (units of conductance), a constant activation energy per carrier $E_a$ and the
Boltzmann constant $k_B$ (a molar activation energy uses $R$ instead). Equivalently
$\ln(G/G_0) = -(E_a/k_B)(1/T)$, so

$$
\frac{d\ln G}{d(1/T)} = -\frac{E_a}{k_B} ,
$$

and for $E_a > 0$ the conductance increases strictly with $T$ on the window. A conductivity version
$\sigma = \sigma_0\exp(-E_a/k_BT)$ is the same model with its own prefactor (equal to $G_0$ times a fixed
geometric factor only for fixed sample geometry). Thermally activated conductance need not follow one such law: a sum of
two Arrhenius channels with different activation energies is not of this form, and data with distinct regions are
fitted window by window.

## Context

Undergraduate level. Most reported conductive MOFs show semiconducting, thermally activated conductance; tabulated activation energies (for example 0.27 eV for Fe2(DSBDC) against 0.41 eV for Fe2(DOBDC)) come from this model, and pellet values also include grain-boundary contributions.

## Depends on

None.

## Proof depends on

- [The Arrhenius rate increases strictly with temperature when Ea > 0](arrhenius-strict-mono.md)

## Expansion

The monotonicity is the generic Arrhenius result with prefactor $G_0$ and $R$ replaced by $k_B$ (equivalently with
the activation temperature $E_a/k_B$). The slope is the derivative of an affine function of $1/T$.

## Sources

- L. Sun, C. H. Hendon, M. A. Minier, A. Walsh and M. Dincă, "Million-Fold Electrical Conductivity Enhancement in Fe2(DEBDC) versus Mn2(DEBDC) (E = S, O)", *Journal of the American Chemical Society* 137, 6164 (2015), [doi.org](https://doi.org/10.1021/jacs.5b02897), PMC4442594, Eq. (1) and Table 1.
- L. S. Xie, G. Skorupskii and M. Dincă, "Electrically Conductive Metal–Organic Frameworks", *Chemical Reviews* 120, 8536–8580 (2020), [doi.org](https://doi.org/10.1021/acs.chemrev.9b00766), PMC7453401, Section 1.1 ($\sigma = \sigma_0\exp(-E_a/kT)$ for semiconductors).
