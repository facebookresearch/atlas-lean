# Loading-independent isosteric enthalpy of a Langmuir isotherm

For a Langmuir isotherm with temperature-independent capacity, the isosteric enthalpy at each temperature is the same at every loading; with a van 't Hoff affinity it equals the constant $\Delta H$.

Let $q(P,T) = q_{\max}\,b(T)P/(1+b(T)P)$ for $T > 0$, with constant $q_{\max} > 0$ and a positive differentiable
affinity $b(T)$. For every loading $0 < q < q_{\max}$ the equilibrium pressure is
$P(q,T) = q/(b(T)(q_{\max}-q))$ and, at temperature $T$,

$$
\Delta H_{ads}(q,T) = R\left(\frac{\partial\ln P}{\partial(1/T)}\right)_{q} = -R\,\frac{d\ln b}{d(1/T)},
$$

which does not depend on $q$. If moreover $b(T) = b_0\exp(-\Delta H/RT)$ with $b_0 > 0$, then
$\Delta H_{ads}(q,T) = \Delta H$ for all $q$ and $T$. A temperature-dependent capacity $q_{\max}(T)$ can make the
isosteric enthalpy depend on loading.

## Context

Graduate level. This is the energetically homogeneous reference case; a loading-dependent isosteric heat measured on a framework points to distinct binding sites or to adsorbate–adsorbate interactions.

## Depends on

- [Langmuir isotherm](langmuir-isotherm.md)
- [Isosteric enthalpy of adsorption](isosteric-enthalpy-of-adsorption.md)

## Proof depends on

None.

## Expansion

From $\ln P = \ln q - \ln(q_{\max} - q) - \ln b(T)$, the only temperature dependence at fixed $q$ is
$-\ln b(T)$; for the van 't Hoff form $\ln b = \ln b_0 - (\Delta H/R)(1/T)$, whose derivative in $1/T$ is
$-\Delta H/R$.

## Sources

- L. Zhang, M. D. Allendorf, R. Balderas-Xicohténcatl, D. P. Broom, G. S. Fanourgakis, G. E. Froudakis, T. Gennett, K. E. Hurst, S. Ling, C. Milanese, P. A. Parilla, D. Pontiroli, M. Riccò, S. Shulda, V. Stavila, T. A. Steriotis, C. J. Webb, M. Witman and M. Hirscher, "Fundamentals of hydrogen storage in nanoporous materials", *Progress in Energy* 4, 042013 (2022), [doi.org](https://doi.org/10.1088/2516-1083/ac8d44), section 2.1 (the Langmuir case: energetically equivalent sites, no adsorbate–adsorbate interactions,
$\Delta H_{st}$ constant as a function of loading).
- R. Nix, *Surface Science*, LibreTexts Chemistry (Queen Mary, University of London), Section 3.3, "Langmuir Isotherm from a Kinetics Consideration", Assumptions 1 and 2 and the displayed equations $P(1-\theta)/\theta = B(T)$ and $\theta = bP/(1+bP)$, [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Surface_Science_%28Nix%29/03:_The_Langmuir_Isotherm/3.03:_Langmuir_Isotherm_from_a_Kinetics_Consideration).
