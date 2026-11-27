# Population attributable fraction: the Levin and Miettinen formulas

Let a binary exposure have population prevalence $p_e = P(E)$, let $\mathrm{RR} = P(D \mid E)/P(D \mid \bar E)$, and suppose $\mathrm{RR}$ is causal: removing the exposure would bring the risk of the exposed to $P(D \mid \bar E)$. The population attributable fraction, the proportion of cases that would not have occurred had the exposure been eliminated, is then

$$\mathrm{PAF} = \frac{P(D) - P(D \mid \bar E)}{P(D)} = \frac{p_e (\mathrm{RR} - 1)}{1 + p_e(\mathrm{RR} - 1)} = p_c\, \frac{\mathrm{RR} - 1}{\mathrm{RR}},$$

the first form being Levin's formula and the second Miettinen's, with $p_c = P(E \mid D) = p_e \mathrm{RR}/(1 + p_e(\mathrm{RR} - 1))$ the prevalence of exposure among cases; both follow from $P(D) = P(D \mid \bar E)(1 + p_e(\mathrm{RR} - 1))$ and Bayes' rule. When the association is confounded, the Miettinen formula with a confounding-adjusted relative risk (or its generalization over strata or exposure levels) gives a confounding-adjusted attributable fraction, whereas Levin's formula with the adjusted relative risk does not; Khosravi et al. (2021) report that of 43 textbooks, 29 propose Levin's formula and only 4 recommend Miettinen's for confounding adjustment.

## Expansion

1. The model: a binary exposure and disease, the counterfactual risk without exposure, and the definition of the attributable fraction.
2. The Levin form from $P(D) = P(D \mid \bar E)(1 + p_e(\mathrm{RR} - 1))$ under no confounding.
3. The Miettinen form via $p_c$ by Bayes' rule, and the algebraic identity of the two forms.
4. The confounded case: with strata $k$ of a confounder, $\mathrm{PAF} = \sum_k P(k \mid D)\, p_{c,k}(\mathrm{RR}_k - 1)/\mathrm{RR}_k$, which reduces to the Miettinen form with a common adjusted $\mathrm{RR}$; and an example where Levin's form with the adjusted $\mathrm{RR}$ is wrong.
5. The generalized impact fraction and the preventable fraction, as separate statements.

## Sources

- A. Khosravi, M. Nazemipour, T. Shinozaki and M. A. Mansournia, Population attributable fraction in textbooks: time to revise, Glob. Epidemiol. 3 (2021), 100062. <https://doi.org/10.1016/j.gloepi.2021.100062>
- Original result: M. L. Levin, The occurrence of lung cancer in man, Acta Unio Int. Contra Cancrum 9 (1953), 531–541. The formula and its use for lung cancer and smoking follow Khosravi et al. (2021).
- Original result: O. S. Miettinen, Proportion of disease caused or prevented by a given exposure, trait or intervention, Am. J. Epidemiol. 99 (1974), 325–332. <https://doi.org/10.1093/oxfordjournals.aje.a121617> The case-prevalence formula and its use with adjusted relative risks follow Khosravi et al. (2021).
