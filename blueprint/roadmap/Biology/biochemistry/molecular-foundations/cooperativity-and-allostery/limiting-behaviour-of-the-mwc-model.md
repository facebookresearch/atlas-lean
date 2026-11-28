# Limiting behaviour of the MWC model

In the Monod–Wyman–Changeux model the fraction of molecules in the relaxed state runs from $1/(1+L)$ without ligand to $1/(1+Lc^n)$ at saturating ligand, and the saturation curve reduces to a hyperbola when the allosteric equilibrium is frozen ($L\to0$ or $L\to\infty$), when the two affinities coincide ($c=1$), or when there is one site.

**Setting.** The [MWC model](mwc-concerted-allosteric-model.md) with $n\ge1$, $L>0$, finite $K_R,K_T>0$ (so $c=K_R/K_T>0$), $\alpha=x/K_R\ge0$, saturation $Y(\alpha)$ and relaxed-state fraction $p_R(\alpha)$.

**Statement.**

1. $Y(0)=0$ and $Y(\alpha)\to1$ as $\alpha\to\infty$.
2. The relaxed-state fraction has the limits

$$p_R(0)=\frac{1}{1+L},\qquad \lim_{\alpha\to\infty}p_R(\alpha)=\frac{1}{1+Lc^{\,n}},$$

When $0<c<1$ and $R$ is the active state, the two limits are the basal activity ("leakiness") and the maximal activity, and their difference $\frac{1}{1+Lc^n}-\frac{1}{1+L}>0$ is the dynamic range of a single molecule; for $c>1$ the roles of minimum and maximum are exchanged and the signed difference is negative.
3. For each fixed $\alpha\ge0$: as $L\to0$, $Y\to\alpha/(1+\alpha)=x/(K_R+x)$; as $L\to\infty$, $Y\to c\alpha/(1+c\alpha)=x/(K_T+x)$.
4. If $c=1$, then $Y=\alpha/(1+\alpha)$ for every $L$: with equal affinities the binding curve carries no information about $L$ and shows no cooperativity.
5. If $n=1$, then

$$Y=\frac{\alpha(1+Lc)}{(1+\alpha)+L(1+c\alpha)},$$

a hyperbolic function of $\alpha$, so sigmoidal saturation needs $n\ge2$.

## Context

Undergraduate to graduate. These limits are the quickest checks on any fitted allosteric model and isolate the parameters that set basal activity, maximal activity and switching range. Marzen, Garcia and Phillips use the two activity limits of an open-favoured ligand-gated channel to define its dynamic range (multiplied by the number of receptors for a population).

## Depends on

- [Monod–Wyman–Changeux concerted allosteric model](mwc-concerted-allosteric-model.md)

## Proof depends on

None.

## Expansion

Proof: for item 2, write $1/p_R=1+L\big((1+c\alpha)/(1+\alpha)\big)^n$; the ratio $(1+c\alpha)/(1+\alpha)$ starts at $1$, tends to $c$, and has derivative $(c-1)/(1+\alpha)^2$, which gives the limits. Derived here and not stated in the cited sources: by the sign of that derivative $p_R$ is strictly increasing in $\alpha$ if $0<c<1$, constant if $c=1$ and strictly decreasing if $c>1$. For item 1 divide $Y$ by $\alpha^n$: numerator and denominator both tend to $1+Lc^n$. Items 3–5 follow by direct substitution, using $\alpha(1+\alpha)^{n-1}/(1+\alpha)^n=\alpha/(1+\alpha)$; item 5 is a ratio of affine functions of $\alpha$, hence hyperbolic. Marzen et al. state item 2 for a two-site channel (their Eqs. 15–16, with $L=e^{-\beta\varepsilon}$ and $c=K_d^{(O)}/K_d^{(C)}$); the $n$-site form is the same computation applied to their Eq. 8.

Remaining decomposition before the page can be marked ready: each item is elementary, but the page relies on the MWC definition page, whose own decomposition (see its Expansion) must be completed first; "hyperbolic" in item 5 should be stated as an explicit Möbius form.

## Sources

- S. Marzen, H. G. Garcia and R. Phillips, "Statistical mechanics of Monod–Wyman–Changeux (MWC) models", *Journal of Molecular Biology* (2013); author manuscript read at [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3786005/), Eq. 8 ($n$-site activity), Eqs. 14–16 (open probability of a two-site channel and its limits $p_{\mathrm{open}}^{\min}=1/(1+e^{-\beta\varepsilon})$ and $p_{\mathrm{open}}^{\max}=1/(1+e^{-\beta\varepsilon}(K_d^{(O)}/K_d^{(C)})^2)$) and Eq. 18 (population dynamic range).
- H. Jakubowski and P. Flatt, *Fundamentals of Biochemistry*, LibreTexts, Section 5.11 "Derivation of the MWC Equation", subsection "Limiting-cases" (a)–(f), [bio.libretexts.org](https://bio.libretexts.org/Bookshelves/Biochemistry/Fundamentals_of_Biochemistry_%28Jakubowski_and_Flatt%29/01%3A_Unit_I-_Structure_and_Catalysis/05%3A_Protein_Function/5.11%3A_Derivation_of_the_MWC_Equation).
