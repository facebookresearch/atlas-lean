# Identifiability of the plasma concentration profile from two interstitial-fluid sites

Let $C_P(t)$ be the plasma drug concentration and let $C_1(t)$, $C_2(t)$ be the concentrations at two sites in the interstitial fluid, each exchanging passively with plasma:

$$\frac{dC_1}{dt} = k_1\,\big(C_P(t) - C_1(t)\big), \qquad \frac{dC_2}{dt} = k_2\,\big(C_P(t) - C_2(t)\big), \qquad k_1, k_2 > 0,$$

with $C_1 = C_2 = C_P = 0$ before $t = 0$. The parameters (the rate constants and the whole profile $C_P$) are called uniquely identifiable from an output $y$ if any two non-identical sets of parameter values give distinct outputs.

1. With a single site, $k_1$ and $C_P$ are not uniquely identifiable from $C_1$ alone (and likewise for $k_2$ and $C_P$ from $C_2$).
2. With both sites, $k_1$, $k_2$ and $C_P$ are uniquely identifiable from $(C_1, C_2)$ provided $k_1 \ne k_2$.

## Depends on

- [Equality of plasma and interstitial-fluid AUC under passive exchange](plasma-and-interstitial-fluid-auc-equality.md)

## Expansion

At one site the ODE can be inverted for any trial rate: given $C_1$ and any $k_1' > 0$, the profile $C_P' = C_1 + C_1'/k_1'$ with $C_1'$ the derivative reproduces exactly the same $C_1$, so a one-parameter family of plasma profiles explains the data. With two sites the plasma profile must satisfy both inversions, $C_P = C_1 + \dot C_1 / k_1 = C_2 + \dot C_2 / k_2$, which ties $1/k_1$ and $1/k_2$ to the two observed curves and removes the freedom when the two sites have different exchange rates. The source proves the statement as Theorem 2 (proof in its Supporting Information) and illustrates the one-site ambiguity for a plasma compartment with first-order elimination, where two distinct pairs $(k_E, k_D)$ always give the same ISF curve (its Proposition S2). It then fits $C_P$ either by maximum likelihood under an assumed sum-of-exponentials order with selection by BIC, or by a spline-based minimum-assumptions fit.

## Sources

- M. K. Erdal, T. E. Kippin, J. P. Hespanha, K. W. Plaxco, Methods of estimating plasma pharmacokinetics from minimally invasive, high temporal resolution measurements of interstitial fluid drug concentrations, Clin. Transl. Sci. 18 (2025), e70248, Definition 2, Theorem 2 and Eq. (2). <https://doi.org/10.1111/cts.70248> (PMCID: PMC12224287)
