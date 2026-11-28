# Zipper (single-stretch) approximation of the helix–coil transition

If at most one helical stretch is allowed, the Zimm–Bragg partition function becomes $q_{\mathrm{zip}}(n)=1+\sigma\sum_{k=1}^{n}(n-k+1)s^k$, which for $s\neq1$ has the closed form $1+\frac{\sigma s^2}{(s-1)^2}\left(s^n+\frac ns-(n+1)\right)$.

**Setting.** The [Zimm–Bragg model](zimm-bragg-helix-coil-model.md) restricted to configurations with $\nu_H\in\{0,1\}$ (the single-stretch or zipper ensemble), with $s,\sigma>0$ and $n\ge1$. For $n\le2$ this is the full Zimm–Bragg ensemble; for $n\ge3$ the restriction is a modelling choice (reasonable for short chains with a large nucleation penalty), not a consequence of the model.

**Statement.**

1. A single helical stretch of $k$ segments can be placed in $n-k+1$ positions, so

$$q_{\mathrm{zip}}(n)=1+\sigma\sum_{k=1}^{n}(n-k+1)\,s^{k},$$

and for $s\neq1$

$$q_{\mathrm{zip}}(n)=1+\frac{\sigma s^2}{(s-1)^2}\left(s^{n}+\frac{n}{s}-(n+1)\right).$$

The probability of the class with $k\ge1$ helical segments is $(n-k+1)\sigma s^k/q_{\mathrm{zip}}(n)$, the all-coil probability is $1/q_{\mathrm{zip}}(n)$, and for $s\neq1$ the helicity is

$$\theta_H=\frac{s}{n}\,\frac{\partial\ln q_{\mathrm{zip}}}{\partial s}=\frac{\sigma s}{(s-1)^3}\cdot\frac{ns^{n+2}-(n+2)s^{n+1}+(n+2)s-n}{n\left(1+\dfrac{\sigma s}{(s-1)^2}\big(s^{n+1}+n-(n+1)s\big)\right)}.$$

2. At $s=1$ (where the closed forms have removable singularities),

$$q_{\mathrm{zip}}(n)\big|_{s=1}=1+\frac{\sigma n(n+1)}{2},\qquad \theta_H\big|_{s=1}=\frac{\sigma(n+1)(n+2)}{6\,q_{\mathrm{zip}}(n)|_{s=1}}.$$

3. $\theta_H$ is strictly increasing in $s$, so the midpoint $\theta_H=1/2$ occurs at a unique $s_{1/2}$, and $s_{1/2}>1$ if and only if $\sigma(n+1)(4-n)<6$. This holds for every $n$ when $0<\sigma<1$ and for every $\sigma$ when $n\ge4$; it fails, for example, for $n=1$, $\sigma=2$, where $s_{1/2}=1/2$.

A chain in the zipper ensemble still has partial helicities; the model is not the same as an all-or-none (two-state) transition.

## Context

Graduate biophysics. The zipper model is the short-chain counterpart of the full Zimm–Bragg treatment and shows how the transition midpoint depends on chain length in the cooperative regime $\sigma<1$. No Artzi-specific result depends on this page.

## Depends on

- [Zimm–Bragg model of the helix–coil transition](zimm-bragg-helix-coil-model.md)

## Proof depends on

- [Mean occupancy as a logarithmic derivative of the binding polynomial](../cooperativity-and-allostery/mean-occupancy-as-logarithmic-derivative.md)

## Expansion

Proof: count placements of one run of length $k$ in a word of length $n$ (there are $n-k+1$), then sum the arithmetico-geometric series using $\sum_{k=1}^n s^k=(s^{n+1}-s)/(s-1)$ and $\sum_{k=1}^n ks^k=s\,(ns^{n+1}-(n+1)s^n+1)/(s-1)^2$; the helicity follows by differentiating in $s$. Item 2 uses $\sum_k(n-k+1)=n(n+1)/2$ and $\sum_kk(n-k+1)=n(n+1)(n+2)/6$. For item 3, $s\,d\theta_H/ds=\operatorname{Var}(n_H)/n>0$ (the same variance identity as for binding polynomials), and $s_{1/2}>1$ iff $\theta_H(1)<1/2$, which rearranges to $\sigma(n+1)(4-n)<6$; the factor $(n+1)(4-n)$ is at most $6$ (at $n=1,2$) and is $\le0$ for $n\ge4$. The closed forms, item 2 and the midpoint examples were checked numerically against brute-force enumeration and bisection.

Remaining decomposition before the page can be marked ready: the variance identity $s\,d\langle n_H\rangle/ds=\operatorname{Var}(n_H)$ for polynomial partition functions as a lemma (it is the analogue of the first step on the [Hill-slope page](../cooperativity-and-allostery/hill-slope-as-variance-ratio.md)), and the series identities as lemmas.

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Section 18.1 "Helix–Coil Transition", subsection "Zipper model" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_%28Tokmakoff%29/05:_Cooperativity/18:_Cooperativity/18.01:_HelixCoil_Transition)): placement count $n-n_H+1$, the sum and its closed form, the distribution $P_H(n,n_H)$ and the helicity formula; the finite-chain paragraph of "Multiple stretches" (midpoint at $s>1$ for cooperative parameters).
