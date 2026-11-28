# Subtype-free average causal effect

Let $A \in \{0,1\}$ be a binary exposure, $X$ baseline covariates, and $Y \in \{0, 1, 2\}$ the disease status (free, subtype 1, subtype 2) at the end of follow-up, with potential outcomes $Y^a$; write $Y_k^a = \mathbf 1[Y^a = k]$, so $Y_1^a Y_2^a = 0$ (subtypes are mutually exclusive). The total effect $\mathbb E[Y_1^1 - Y_1^0]$ can be non-zero purely because the exposure switches some people from subtype 1 to subtype 2. The **subtype-free average causal effect** for subtype 1 is the principal-stratum effect

$$\mathrm{SF\text{-}ACE}_1 = \mathbb E\big[Y_1^1 - Y_1^0 \,\big|\, Y_2^0 = Y_2^1 = 0\big],$$

the average effect on subtype 1 among those who would be free of subtype 2 under either exposure level; $\mathrm{SF\text{-}ACE}_2$ is defined symmetrically, and $\mathrm{SF\text{-}ACE}_1 - \mathrm{SF\text{-}ACE}_2$ measures heterogeneity of the effect across subtypes.

**Assumptions.** SUTVA, weak ignorability $Y^a \perp A \mid X$, positivity, and
- *S-monotonicity for subtype $k$*: $Y_k^0 \le Y_k^1$ (the exposure cannot prevent subtype $k$);
- *D-monotonicity for subtype $k$*: $Y_k^0 = 1 \Rightarrow Y^1 \ne 0$ (the exposure cannot prevent disease in someone who would have subtype $k$, though it may change the subtype).

**Proposition.**
1. Under the standard assumptions alone, $\mathrm{SF\text{-}ACE}_k$ is not point identified, only partially identified by large-sample bounds.
2. Under S-monotonicity for both subtypes there is no subtype switching, the stratum $\{Y_2^0 = Y_2^1 = 0\}$ equals $\{Y_2^1 = 0\}$, and

$$\mathrm{SF\text{-}ACE}_1 = \frac{P(Y^1 = 1) - P(Y^0 = 1)}{1 - P(Y^1 = 2)}, \qquad P(Y^a = k) = \mathbb E_X\big[P(Y = k \mid A = a, X)\big],$$

so it is the total effect rescaled by the probability of being free of subtype 2 under exposure, and is close to the total effect when that subtype is rare.
3. Replacing S-monotonicity by D-monotonicity for a subtype permits switching and loses point identification; bounds narrow under D-monotonicity for subtype 1 and S-monotonicity for subtype 2, and with D-monotonicity for both subtypes the estimand is identified once the (unidentifiable but bounded) subtype-switching probabilities are fixed, which yields a sensitivity analysis.

## Expansion

Part 2: under S-monotonicity for subtype 2, $Y_2^1 = 0$ forces $Y_2^0 = 0$, so the principal stratum is $\{Y_2^1 = 0\}$. Mutual exclusivity gives $\{Y_1^1 = 1\} \subseteq \{Y_2^1 = 0\}$, and S-monotonicity for subtype 1 gives $\{Y_1^0 = 1\} \subseteq \{Y_1^1 = 1\} \subseteq \{Y_2^1 = 0\}$; hence $\mathbb E[(Y_1^1 - Y_1^0)\mathbf 1(Y_2^1 = 0)] = P(Y_1^1 = 1) - P(Y_1^0 = 1)$, and dividing by $P(Y_2^1 = 0)$ gives the formula. Each counterfactual marginal is identified by standardization (or inverse-probability weighting, or their augmented doubly robust combination) under ignorability and positivity. The estimand is a survivor-average-causal-effect analogue in which each subtype plays in turn the role of the outcome and of the truncating event. Because $\mathrm{SF\text{-}ACE}_1$ and $\mathrm{SF\text{-}ACE}_2$ live on different (though, for rare diseases, heavily overlapping) latent strata, a non-zero difference signals effect heterogeneity without pinning down its source.

## Sources

- A. Sasson, M. Wang, S. Ogino, D. Nevo, "The subtype-free average causal effect for heterogeneous disease etiology", Biometrics 81(1) (2025) ujaf016, Section 5 (Eq. (5)), Assumptions 1–2 and Propositions 1–4, <https://doi.org/10.1093/biomtc/ujaf016>, PMCID PMC11848129.
