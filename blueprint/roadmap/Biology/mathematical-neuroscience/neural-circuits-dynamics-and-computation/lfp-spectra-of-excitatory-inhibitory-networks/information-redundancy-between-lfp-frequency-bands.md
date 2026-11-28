# Information redundancy between LFP frequency bands

Let $S$ be a stimulus drawn from a finite set with probabilities $P(s)$, and let $R_1$, $R_2$ be discrete-valued neural responses, such as the LFP power at frequencies $f_1$ and $f_2$ (discretized into bins). The information that $R_1$ carries about $S$ is

$$I(S; R_1) \;=\; \sum_{s} P(s) \sum_{r} P(r \mid s)\, \log_2 \frac{P(r \mid s)}{P(r)},$$

and $I(S; R_1, R_2)$ is defined likewise for the joint response. The information redundancy is

$$\mathrm{Red}(R_1, R_2) \;=\; I(S; R_1) + I(S; R_2) - I(S; R_1, R_2).$$

Then:

1. $\mathrm{Red}(R_1, R_2) = I(R_1; R_2) - I(R_1; R_2 \mid S)$, so redundancy is the shared information between the two responses minus the part of it that persists at fixed stimulus.
2. If $R_1$ and $R_2$ are conditionally independent given $S$ (no shared noise), then $\mathrm{Red} = I(R_1; R_2) \ge 0$, with equality if and only if $R_1$ and $R_2$ are independent.
3. $\mathrm{Red} > 0$ means overlapping information (redundant channels), $\mathrm{Red} = 0$ means the two responses contribute independently, and $\mathrm{Red} < 0$ means synergy, where joint observation reveals more than the sum of the parts.

Positive redundancy can arise from similar stimulus tuning (signal correlation) or from shared noise (noise correlation); the two are separated by correlating trial-averaged responses across stimuli and trial-by-trial fluctuations at fixed stimulus.

## Depends on

- [Current-sum LFP proxy of an integrate-and-fire network](current-sum-lfp-proxy-of-an-integrate-and-fire-network.md)

## Expansion

Write each mutual information as an entropy difference: $I(S;R_1) + I(S;R_2) - I(S;R_1,R_2) = [H(R_1) + H(R_2) - H(R_1,R_2)] - [H(R_1|S) + H(R_2|S) - H(R_1,R_2|S)]$, which is $I(R_1;R_2) - I(R_1;R_2|S)$; this gives item 1. Conditional independence makes the second term vanish, giving item 2, since mutual information is nonnegative and zero exactly under independence. In practice the plug-in estimates are biased upward by limited sampling, so they are corrected by shuffling, quadratic extrapolation and bootstrap subtraction. In the excitatory–inhibitory network, pairs of gamma-band frequencies above $50$ Hz were highly redundant, with joint information on average $0.51$ bits below the sum, about $60\%$ of the information of the less informative frequency. Low-frequency bands carried nearly independent information, entrained by the corresponding slow components of the input, and the low-frequency and gamma channels represented naturalistic stimuli largely independently.

## Sources

- A. Mazzoni, S. Panzeri, N. K. Logothetis, N. Brunel, "Encoding of naturalistic stimuli by local field potential spectra in networks of excitatory and inhibitory neurons", *PLoS Computational Biology* 4(12) (2008) e1000239, Results (Figure 4C–D) and Methods, "Measures of Information Carried by the Neural Response Power" (Equations 12–14), <https://doi.org/10.1371/journal.pcbi.1000239> (PMC2585056).
