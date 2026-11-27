# Functional impact score from family and subfamily conservation

Let the sequences of a protein family alignment be partitioned into subfamilies (in the source, by combinatorial-entropy clustering that maximizes the difference of residue distributions between subfamilies at a set of specificity positions), and let $p$ be the subfamily containing the mutated protein. Write $n_{i,p}(\alpha)$ for the number of residues of type $\alpha$ at alignment position $i$ within subfamily $p$. For a substitution $\alpha \to \beta$ at position $i$, define the family [conservation score](combinatorial-entropy-conservation-score.md) $\Delta S_i^{\mathrm c}(\alpha \to \beta) = \ln\big(n_i(\alpha)/(n_i(\beta)+1)\big)$, the **specificity score**

$$\Delta S_i^{\mathrm s}(\alpha \to \beta) = \ln \frac{n_{i,p}(\alpha)}{n_{i,p}(\beta) + 1},$$

and the **functional impact score**

$$\mathrm{FIS}_i(\alpha \to \beta) = \tfrac12\Big(\Delta S_i^{\mathrm c}(\alpha \to \beta) + \Delta S_i^{\mathrm s}(\alpha \to \beta)\Big).$$

**Properties.** If the family consists of a single subfamily, $\mathrm{FIS} = \Delta S^{\mathrm c}$. If $N_p$ is the size of subfamily $p$ and $N$ the family size, then $-\tfrac12(\ln N + \ln N_p) \le \mathrm{FIS} \le \tfrac12(\ln N + \ln N_p)$. A substitution at a position conserved within subfamily $p$ but variable across the family (a specificity residue) receives a high specificity score even when its family conservation score is moderate.

## Depends on

- [Combinatorial-entropy conservation score of a substitution](combinatorial-entropy-conservation-score.md)

## Remarks

The specificity score is the combinatorial-entropy change computed inside the subfamily, so the bounds are those of the family score applied to $N$ and $N_p$ and averaged. Family conservation captures constraints on overall function; subfamily conservation captures specificity of interaction partners or substrates, whose alteration can switch rather than abolish function. The source compared taking the maximum of the two scores with their average and found the average more accurate. Calibrated on about 19,200 disease-associated variants versus about 35,600 common polymorphisms, the score reached an area under the ROC curve of about 0.86, with balanced accuracy about 79% at a threshold of about 1.9; impact classes neutral, low, medium and high were defined by cutoffs 0.8, 1.9 and 3.5. Recurrent somatic mutations in cancer and mutations in known oncogenes and tumour suppressors are enriched in high scores.

## Sources

- B. Reva, Y. Antipin and C. Sander, "Predicting the functional impact of protein mutations: application to cancer genomics", Nucleic Acids Research 39 (2011) e118, Materials and Methods, Equations (4)–(7); Results (validation test, Figures 2–3, Table 1), <https://doi.org/10.1093/nar/gkr407>, PMCID PMC3177186.
