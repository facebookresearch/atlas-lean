# Protein stability curve with constant heat-capacity change

If unfolding has a temperature-independent heat-capacity change $\Delta C_p$, the unfolding free energy of a two-state protein is $\Delta G(T)=\Delta H_0(1-T/T_m)+\Delta C_p\,(T-T_m-T\ln(T/T_m))$; for $\Delta C_p>0$ this "stability curve" is strictly concave and can cross zero twice, giving heat and cold denaturation.

**Setting.** Two-state unfolding $N\rightleftharpoons U$ as on [two-state unfolding](two-state-unfolding-and-the-van-t-hoff-slope.md), now with a heat-capacity change $\Delta C_p=C_p^U-C_p^N$ that is constant in temperature. Let $T_m>0$ be a temperature where $\Delta G(T_m)=0$ and $\Delta H_0=\Delta H(T_m)$ the unfolding enthalpy there.

**Statement.**

1. For all $T>0$,

$$\Delta H(T)=\Delta H_0+\Delta C_p\,(T-T_m),\qquad \Delta S(T)=\frac{\Delta H_0}{T_m}+\Delta C_p\ln\frac{T}{T_m},$$

$$\Delta G(T)=-RT\ln K_{NU}(T)=\Delta H_0\left(1-\frac{T}{T_m}\right)+\Delta C_p\left(T-T_m-T\ln\frac{T}{T_m}\right).$$

With $\Delta C_p=0$ this reduces to the affine free energy of the two-state page.

2. Suppose $\Delta C_p>0$ and $\Delta H_0>0$, so that $T_m$ is a heat-denaturation midpoint ($\Delta G$ decreases through zero there, with slope $-\Delta H_0/T_m$). Then $\Delta G$ is strictly concave on $T>0$, attains its maximum at $T_s=T_m\exp\!\big(-\Delta H_0/(T_m\Delta C_p)\big)$, and has a second zero $T_{\mathrm{cold}}\in(0,T_m)$ (cold denaturation) if and only if $0<\Delta H_0/(T_m\Delta C_p)<1$; there are never more than two zeros.

Seelig and Seelig give the approximation $T_{\mathrm{cold}}\approx T_m\,(2e^{-a}-1)$ with $a=\Delta H_0/(T_m\Delta C_p)$. It has no general accuracy guarantee: it becomes negative for $a>\ln 2$ although an exact positive root exists for all $0<a<1$ (for $a=0.8$ the exact root is about $0.07\,T_m$ while the approximation is negative). The exact root should be computed from item 1.

## Context

Undergraduate to graduate biophysics. The stability curve explains why proteins have a temperature of maximal stability and can unfold on cooling, and it is the model behind differential scanning calorimetry fits; whether $\Delta C_p$ is constant for a given protein is an empirical question. Formulation science for protein therapeutics delivered from depots relies on such stability analysis, but no Artzi publication read for this roadmap uses it directly.

## Depends on

- [Two-state unfolding equilibrium and the van 't Hoff slope at the melting temperature](two-state-unfolding-and-the-van-t-hoff-slope.md)

## Proof depends on

None.

## Expansion

Proof: integrate $d\Delta H/dT=\Delta C_p$ and $d\Delta S/dT=\Delta C_p/T$ from $T_m$, use $\Delta S(T_m)=\Delta H_0/T_m$ (from $\Delta G(T_m)=0$), and form $\Delta G=\Delta H-T\Delta S$. For item 2: $d\Delta G/dT=-\Delta S(T)$ and $d^2\Delta G/dT^2=-\Delta C_p/T<0$; the maximum is where $\Delta S(T_s)=0$; $\Delta G(T)\to\Delta H_0-T_m\Delta C_p$ as $T\to0^+$ (since $T\ln T\to0$); by concavity, $\Delta G>0$ just below $T_m$, so a zero in $(0,T_m)$ exists iff this limit is negative, i.e. $a<1$; a strictly concave function has at most two zeros. The numerical example was checked by bisection.

Remaining decomposition before the page can be marked ready: a lemma on the existence and uniqueness of the zeros of a strictly concave continuous function with the given boundary behaviour (available from standard real analysis), and an explicit statement that constant $\Delta C_p$ is a modelling assumption.

## Sources

- J. Seelig and A. Seelig, "Protein unfolding—thermodynamic perspectives and unfolding models", *International Journal of Molecular Sciences* 24(6) (2023), 5457, [www.mdpi.com](https://www.mdpi.com/1422-0067/24/6/5457); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC10049513/), Section 2.2, Eqs. 8–10 (enthalpy, entropy and free energy with constant $\Delta C_p^0$) and Eqs. 13–14 (approximate cold-denaturation temperature and the gap between heat and cold denaturation).
- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Section 18.2 "Two-State Thermodynamics" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_%28Tokmakoff%29/05%3A_Cooperativity/18%3A_Cooperativity/18.02%3A_Two-State_Thermodynamics)), final equation (the same functional form in the folding direction).
