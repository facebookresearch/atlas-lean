# Closed-form complex concentration of a single binding equilibrium

**Setting.** Two species $A$ and $B$ form a complex $C=A{:}B$ by the reversible reaction $A+B\rightleftharpoons C$ with association and dissociation rates $k^+,k^->0$ and dissociation constant $K=k^-/k^+$. Mass conservation fixes the totals $A_T=A+C$ and $B_T=B+C$. In gene-expression models of cell-free transcription-translation this describes RNA polymerase binding a sigma factor (holoenzyme formation), the holoenzyme binding a constitutive promoter, or ribosomes binding a single mRNA species, all assumed fast compared with elongation.

**Proposition (quasi-steady state).** At equilibrium, $AB=KC$, and the complex concentration is the unique root of

$$C^2-(A_T+B_T+K)\,C+A_TB_T=0$$

in $[0,\min(A_T,B_T)]$, namely

$$C=\frac{A_T+B_T+K-\sqrt{(A_T+B_T+K)^2-4A_TB_T}}{2}.$$

In the limits: if $B_T\ll A_T$ then $C\approx B_T\,\dfrac{A_T}{A_T+K}$ (hyperbolic saturation); if $K\ll A_T,B_T$ then $C\approx\min(A_T,B_T)$ (titration). When several species compete for the same partner (several DNA species for one holoenzyme, several mRNAs for ribosomes) the single-pair formula no longer applies; the source then implements the coupled binding reactions directly as fast reactions, which produces loading effects absent from the single-species formula.

## Expansion

Substituting $A=A_T-C$ and $B=B_T-C$ into $AB=KC$ gives the quadratic. Its discriminant $(A_T+B_T+K)^2-4A_TB_T=(A_T-B_T)^2+2K(A_T+B_T)+K^2$ is positive, and the product and sum of the roots are $A_TB_T$ and $A_T+B_T+K$; evaluating the quadratic at $C=\min(A_T,B_T)$ gives $-K\min(A_T,B_T)\le0$, so exactly one root lies in the physical interval and it is the smaller one. The approximations follow by expanding the square root. In the cited transcription model, the bound holoenzyme $\overline{R{:}\sigma}$ and the activated DNA follow from this formula when only self-competition occurs, which makes transcription act approximately as a static gain and translation as an integrator over short time windows.

## Sources

- Halter W, Murray RM, Allgöwer F, "Analysis of primitive genetic interactions for the design of a genetic signal differentiator", Synth Biol (2019), Section 3.2, Equations (8)-(13) and Proposition 1, <https://doi.org/10.1093/synbio/ysz015>, PMCID PMC7445770.
