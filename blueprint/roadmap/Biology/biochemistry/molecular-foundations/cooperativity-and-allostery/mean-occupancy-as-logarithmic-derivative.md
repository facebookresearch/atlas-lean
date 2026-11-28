# Mean occupancy as a logarithmic derivative of the binding polynomial

The mean number of ligands bound to a multisite macromolecule is the logarithmic derivative of its binding polynomial with respect to the logarithm of the free ligand concentration: $\langle i\rangle=x\,P'(x)/P(x)=d\ln P/d\ln x$ for $x>0$.

**Statement.** Let $P(x)=\sum_{i=0}^N\beta_ix^i$ be an [Adair binding polynomial](adair-binding-polynomial.md) with $\beta_0=1$, $\beta_i\ge0$. For every $x>0$,

$$\langle i\rangle(x)=\frac{x\,P'(x)}{P(x)}=\frac{d\ln P}{d\ln x},\qquad Y(x)=\frac{x}{N}\,\frac{d\ln P}{dx}.$$

At $x=0$ the middle expression extends continuously with value $0$, but the derivative in $\ln x$ is not defined there.

## Context

Undergraduate to graduate. Known as Wyman's binding-potential or linkage relation in the binding literature, the identity turns a binding curve into a derivative of one function, which is what makes linkage and fluctuation arguments (such as the [variance form of the Hill slope](hill-slope-as-variance-ratio.md)) short.

## Depends on

- [Adair binding polynomial and fractional saturation](adair-binding-polynomial.md)

## Proof depends on

None.

## Expansion

Proof: differentiate termwise, $xP'(x)=\sum_i i\beta_ix^i$, and divide by $P(x)>0$ to get $\sum_i i\,p_i(x)$; the chain rule $d/d\ln x=x\,d/dx$ gives the logarithmic form.

Remaining decomposition before the page can be marked ready: an explicit statement of which parameters are held fixed when the coefficients depend on other variables (as for the polynomial partition functions of the [Zimm–Bragg model](../folding-and-hybridization-thermodynamics/zimm-bragg-helix-coil-model.md), whose coefficients depend on the fixed nucleation weight); a power-series form would need its own source and convergence hypothesis.

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Section 18.1 "Helix–Coil Transition", subsection "Non-cooperative Model", derivation of $\langle n\rangle=(s/q)\,\partial q/\partial s=\partial\ln q/\partial\ln s$ for a polynomial partition function with coefficients independent of $s$, [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_%28Tokmakoff%29/05:_Cooperativity/18:_Cooperativity/18.01:_HelixCoil_Transition).
- H. Jakubowski and P. Flatt, *Fundamentals of Biochemistry*, LibreTexts, Section 5.11 "Derivation of the MWC Equation", subsection "The linkage (logarithmic-derivative) relation": $\langle i\rangle=\alpha\,d\ln P/d\alpha$ and $Y=(\alpha/n)\,d\ln P/d\alpha$ for the MWC binding polynomial, [bio.libretexts.org](https://bio.libretexts.org/Bookshelves/Biochemistry/Fundamentals_of_Biochemistry_%28Jakubowski_and_Flatt%29/01%3A_Unit_I-_Structure_and_Catalysis/05%3A_Protein_Function/5.11%3A_Derivation_of_the_MWC_Equation).
