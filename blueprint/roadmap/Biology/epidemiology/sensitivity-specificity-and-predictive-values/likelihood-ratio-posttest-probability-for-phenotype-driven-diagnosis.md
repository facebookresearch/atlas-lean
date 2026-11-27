# Likelihood ratios and posttest probability for ontology-coded phenotypes

For a disease $D$ and a test result $x$, the likelihood ratio is

$$\mathrm{LR}(x) = \frac{\Pr(x \mid D)}{\Pr(x \mid \neg D)} = \frac{\text{sensitivity}}{1 - \text{specificity}} \quad\text{(for a positive result)}.$$

For results $X = (x_1, \dots, x_n)$ that are conditionally independent given $D$ and given $\neg D$, $\mathrm{LR}(X) = \prod_{i=1}^n \mathrm{LR}(x_i)$. With pretest probability $p = \Pr(D)$, the posttest probability is

$$\Pr(D \mid X) = \frac{p\, \mathrm{LR}(X)}{(1 - p) + p\, \mathrm{LR}(X)},$$

that is, posttest odds equal pretest odds times $\mathrm{LR}(X)$.

**Phenotype terms.** In a phenotype ontology (a directed acyclic graph of terms with ancestor sets $\operatorname{anc}(h)$ and child sets $\operatorname{child}(h)$), let $\operatorname{annot}(D)$ be the terms annotating $D$, and let $f_j^D$ be the frequency of term $h_j$ in $D$ (default $1$ if unknown). The numerator of $\mathrm{LR}(h_i) = \Pr(h_i \mid D)/\Pr(h_i \mid \neg D)$ is defined case by case. Three of the cases:

- if $h_i \in \operatorname{annot}(D)$: $\Pr(h_i \mid D) = f_i^D$;
- if $h_i$ is an ancestor of annotating terms: $\Pr(h_i \mid D) = \max\{ f_j^D : h_i \in \operatorname{anc}(h_j),\ h_j \in \operatorname{annot}(D) \}$, by the true-path rule;
- if $h_i$ is a direct child of annotating terms: $\Pr(h_i \mid D) = |\operatorname{child}(h_j)|^{-1} \max\{ f_j^D : h_i \in \operatorname{child}(h_j),\ h_j \in \operatorname{annot}(D) \}$, a penalized partial match.

The exact denominator $\Pr(h_i \mid \neg D)$ averages over the diseases other than the candidate $D$; the source approximates it by the background frequency of $h_i$ across all annotated diseases, $D$ included, and combines the phenotype likelihood ratios by multiplication, which treats the terms as conditionally independent given $D$ and given $\neg D$ although ontology terms of one patient are typically dependent. The resulting $\Pr(D \mid X)$ is therefore a model-based score for ranking candidate diagnoses, not a calibrated probability; the Bayes identity above is exact only for the true $\Pr(X \mid D)$ and $\Pr(X \mid \neg D)$. The factor $\mathrm{LR}(h_i)$ shows how much each observed abnormality contributes to the score.

## Depends on

- [Formula for the positive predictive value](ppv-eq.md)

## Expansion

Bayes' theorem gives $\Pr(D \mid X)/\Pr(\neg D \mid X) = \{\Pr(D)/\Pr(\neg D)\} \cdot \Pr(X \mid D)/\Pr(X \mid \neg D)$, and solving for $\Pr(D \mid X)$ gives the displayed formula. For a single positive test it is the positive predictive value. Conditional independence factorizes the joint likelihood ratio. The ancestor case uses that a patient with any annotated descendant also has the ancestor, so the probability is at least the largest such frequency.

## Sources

- P. N. Robinson, V. Ravanmehr, J. O. B. Jacobsen et al., *Interpretable clinical genomics with a likelihood ratio paradigm*, Am. J. Hum. Genet. 107 (2020), 403–417, <https://doi.org/10.1016/j.ajhg.2020.06.021>, PMCID PMC7477017, Material and Methods: Equations 1–4 (likelihood ratio, multiple tests, posttest probability), Equation 5 (phenotype LR), Equations 6–7 (ancestor and child cases), Equations 8–9 (background denominator and combination of likelihood ratios) and the Limitations section of the Discussion (both approximations).
