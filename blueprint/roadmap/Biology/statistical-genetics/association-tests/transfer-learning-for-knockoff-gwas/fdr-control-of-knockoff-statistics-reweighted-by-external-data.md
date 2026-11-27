# FDR control of knockoff statistics reweighted by external data

**Setting.** In a target population (environment $e=0$) with genotypes $X^0\in\mathbb R^{n\times p}$ and phenotype $Y^0$, test the conditional hypotheses $H^0_j:\ Y^0\perp X^0_j\mid X^0_{-j}$, $j=1,\dots,p$. Model-X knockoffs $\tilde X^0$ are generated from $X^0$ without looking at $Y^0$, so that $\tilde X^0\perp Y^0\mid X^0$ and swapping any null column with its knockoff leaves the joint law invariant. Knockoff statistics $W_j=w_j(X,\tilde X,Y)$ have the *flip-sign property*: swapping $X_j$ and $\tilde X_j$ only changes the sign of $W_j$ (e.g. $W_j=|\hat b_j|-|\hat b_{j+p}|$ from a lasso fit on $[X,\tilde X]$). The knockoff filter at level $q$ rejects $\{j:W_j\ge T\}$ with

$$T=\min\Big\{t>0:\ \frac{1+\#\{j:W_j\le -t\}}{\#\{j:W_j\ge t\}\vee 1}\le q\Big\},$$

and controls the false discovery rate at $q$ whenever the signs of the null $W_j$ are i.i.d. fair coin flips conditional on $(|W_1|,\dots,|W_p|)$. External data from environments $e=1,\dots,E$ (other ancestries or related outcomes) are independent of the target data.

**Proposition 2.1 (linear re-ordering).** Let $W^0$ be computed on the target data and $W^{\mathrm{ext}}$ on the pooled external data, and for a fixed $\theta\in[0,1]$ set

$$\operatorname{sign}W^{\mathrm{lro}}_j=\operatorname{sign}W^0_j,\qquad |W^{\mathrm{lro}}_j|=(1-\theta)|W^0_j|+\theta|W^{\mathrm{ext}}_j| .$$

Then, conditional on $|W^{\mathrm{lro}}|$, the signs of $W^{\mathrm{lro}}_j$ for all true nulls $H^0_j$ are i.i.d. coin flips, so the knockoff filter applied to $W^{\mathrm{lro}}$ controls the FDR in the target population.

**Proposition 2.2 (weighted lasso).** Let prior weights $\phi_1,\dots,\phi_{2p}>0$ depend only on external data or prior knowledge, with $\phi_j=\phi_{j+p}$. Fit on the target data the weighted lasso $\min_b\ \tfrac12\|Y^0-[X^0,\tilde X^0]b\|_2^2+\lambda\sum_{k=1}^{2p}\phi_k|b_k|$ and set $W^{\mathrm{wl}}_j=|\hat b_j|-|\hat b_{j+p}|$. Then the null signs of $W^{\mathrm{wl}}$ are i.i.d. coin flips conditional on $|W^{\mathrm{wl}}|$, and FDR is controlled. **Proposition 2.3:** the same holds when $\phi$ is fitted on the pooled data from all environments including the target, provided every variable null in the target is null in every environment.

## Depends on

- [Knockoff threshold](../../../../Probability/hypothesis-testing/knockoff-filter/knockoff-threshold.md)
- [FDR control by knockoff+](../../../../Probability/hypothesis-testing/knockoff-filter/integral-false-discovery-proportion-knoc.md)

## Expansion

Proposition 2.1: by the flip-sign property and exchangeability, the null signs of $W^0$ are i.i.d. coin flips given $|W^0|$; $W^{\mathrm{ext}}$ is independent of the target data, so conditioning additionally on it, and hence on $|W^{\mathrm{lro}}|$, leaves them fair. External evidence thus only reorders hypotheses, moving likely non-nulls to the end of the sequence the filter scans, which raises power without affecting validity. Proposition 2.2: the symmetric penalty $\phi_j=\phi_{j+p}$ makes the weighted lasso equivariant under swapping a variable with its knockoff, preserving the flip-sign property. Proposition 2.3 swaps null variables with their knockoffs simultaneously in all environments, which leaves the pooled joint law invariant exactly when nulls are shared.

## Sources

- Li S, Ren Z, Sabatti C, Sesia M, "Transfer Learning in Genome-Wide Association Studies with Knockoffs", Sankhya B (2022), Equations (2.1)-(2.5) and Propositions 2.1-2.3, <https://doi.org/10.1007/s13571-022-00297-y>, PMCID PMC12331138.
