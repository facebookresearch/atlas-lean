# Difference-of-sigmoids half-hat response

Let $A > 0$ be the effective strength of a glomerulus's sensory input, set by odor ligand–receptor affinity at fixed concentration and measured in the same units as the half-activation constants. The direct activations of mitral cells and periglomerular cells are Hill sigmoids

$$\{\mathrm{Mi}_{\mathrm{in}}, \mathrm{PG}\} = \frac{K}{1 + (Y_{1/2}/A)^{m}}, \tag{1}$$

with maximal activation $K > 0$, half-activation constant $Y_{1/2} > 0$ and cooperativity $m > 0$, and the mitral-cell output of the model is excitation minus periglomerular inhibition:

$$\mathrm{Mi}_{\mathrm{out}}(A) = \frac{K_e}{1 + (Y_{1/2}^{(e)}/A)^{m_e}} - \frac{K_i}{1 + (Y_{1/2}^{(i)}/A)^{m_i}}. \tag{2}$$

The source studies this model in the regime $K_e > K_i$, $Y_{1/2}^{(e)} < Y_{1/2}^{(i)}$, where excitation is stronger and more sensitive than inhibition.

**Auxiliary properties** (derived here, not stated in the source; proved in the Expansion). With unit cooperativities ($m_e = m_i = 1$), write $Y_e = Y_{1/2}^{(e)}$ and $Y_i = Y_{1/2}^{(i)}$, so that $\mathrm{Mi}_{\mathrm{out}}(A) = K_e A/(A + Y_e) - K_i A/(A + Y_i)$, and assume $K_e > K_i > 0$ and $0 < Y_e < Y_i$. Then:

1. $\mathrm{Mi}_{\mathrm{out}}(A) > 0$ for all $A > 0$, $\mathrm{Mi}_{\mathrm{out}}(A) \to 0$ as $A \to 0$, and $\mathrm{Mi}_{\mathrm{out}}(A) \to K_e - K_i$ as $A \to \infty$;
2. if $K_e Y_e < K_i Y_i$, $\mathrm{Mi}_{\mathrm{out}}$ has a unique interior maximum, at

$$A^{*} = \frac{\sqrt{K_e Y_e}\, Y_i - \sqrt{K_i Y_i}\, Y_e}{\sqrt{K_i Y_i} - \sqrt{K_e Y_e}},$$

increasing on $(0, A^{*})$ and decreasing on $(A^{*}, \infty)$: glomeruli of intermediate affinity respond most, and stronger inputs are suppressed relative to them (a half-hat response);
3. if $K_e Y_e \ge K_i Y_i$, $\mathrm{Mi}_{\mathrm{out}}$ is increasing on $(0, \infty)$ and there is no contrast enhancement.

So within the regime $K_e > K_i$, $Y_e < Y_i$ a half-hat response needs the further condition $K_e Y_e < K_i Y_i$. For example, $K_e = 1$, $K_i = 0.6$, $Y_e = 10^{-5}$ M and $Y_i = 10^{-4}$ M satisfy $K_e Y_e < K_i Y_i$, with $A^{*} \approx 5.2 \times 10^{-5}$ M, while $K_e = 1$, $K_i = 0.6$, $Y_e = 10^{-5}$ M and $Y_i = 1.5 \times 10^{-5}$ M give a monotone response.

## Expansion

The derivative is $K_e Y_e/(A + Y_e)^2 - K_i Y_i/(A + Y_i)^2$, which vanishes when $\sqrt{K_e Y_e}\,(A + Y_i) = \sqrt{K_i Y_i}\,(A + Y_e)$, a linear equation with the single solution $A^{*}$. Its numerator is positive because $K_e Y_i > K_i Y_e$, so $A^{*} > 0$ exactly when the denominator is positive. The derivative has the sign of $\sqrt{K_e Y_e}\,(A + Y_i) - \sqrt{K_i Y_i}\,(A + Y_e)$, which is positive at $A = 0$ and, when $K_e Y_e < K_i Y_i$, decreasing in $A$ with its single zero at $A^{*}$, which gives item 2; when $K_e Y_e \ge K_i Y_i$ it is positive for every $A > 0$, which gives item 3. Positivity follows from $K_e A/(A + Y_e) > K_i A/(A + Y_i)$, which holds because $K_e > K_i$ and $A + Y_e < A + Y_i$, and the limits are those of the two hyperbolic terms. The response is one half of a Mexican-hat (on-centre, inhibitory-surround) profile; rotating it about its maximum in the high-dimensional space of receptor affinities gives contrast enhancement that inherits the similarity structure of the receptor repertoire instead of the spatial layout of glomeruli. The regime $K_e > K_i$, $Y_e < Y_i$ is favoured by the smaller volume and higher input resistance of periglomerular spines compared with mitral dendrites. A separate global feedback loop normalizes for odor concentration.

## Sources

- T. A. Cleland, P. Sethupathy, "Non-topographical contrast enhancement in the olfactory bulb", BMC Neuroscience 7 (2006) 7, Methods, "Illustrative model of NTCE", Eqs. (1) and (2), <https://doi.org/10.1186/1471-2202-7-7> (PMC1368991). The auxiliary properties are the page's own computation for unit cooperativities.
