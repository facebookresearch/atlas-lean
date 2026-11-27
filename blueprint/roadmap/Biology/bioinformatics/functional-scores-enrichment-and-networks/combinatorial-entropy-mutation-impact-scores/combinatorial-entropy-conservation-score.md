# Combinatorial-entropy conservation score of a substitution

Let column $i$ of a multiple sequence alignment of $N \ge 1$ homologous proteins contain $n_i(\alpha)$ symbols of type $\alpha$, where $\alpha$ ranges over the 20 amino acids and the gap, so $\sum_\alpha n_i(\alpha) = N$. The **combinatorial entropy** of the column is the logarithm of the number of distinct arrangements of its symbols,

$$S_i = \ln \frac{N!}{\prod_\alpha n_i(\alpha)!}, \qquad 0! = 1 .$$

A substitution $\alpha \to \beta$ ($\beta \ne \alpha$) in one sequence that carries $\alpha$ at position $i$ (so $n_i(\alpha) \ge 1$) changes the counts to $n_i(\alpha) - 1$ and $n_i(\beta) + 1$.

**Proposition.** The resulting entropy change, used as the family conservation score of the substitution, is

$$\Delta S_i^{\mathrm c}(\alpha \to \beta) = \ln \frac{n_i(\alpha)}{n_i(\beta) + 1}.$$

It is finite even when $\beta$ never occurs in the column, it is the same for every family member carrying $\alpha$ at position $i$, it is positive exactly when $n_i(\alpha) > n_i(\beta) + 1$, and

$$-\ln N \le \Delta S_i^{\mathrm c}(\alpha \to \beta) \le \ln N,$$

with the upper bound attained exactly when the column is fully conserved ($n_i(\alpha) = N$, hence $n_i(\beta) = 0$).

## Remarks

All factorials except those of $\alpha$ and $\beta$ cancel in the difference of entropies after and before the substitution, leaving $\ln\big[n_i(\alpha)!\,n_i(\beta)! / ((n_i(\alpha)-1)!\,(n_i(\beta)+1)!)\big]$. The bounds follow from $1 \le n_i(\alpha) \le N$ and $1 \le n_i(\beta)+1 \le N - n_i(\alpha) + 1 \le N$. A substitution away from a residue conserved across the family toward one rarely or never seen there makes the column less ordered, so its entropy rises sharply; a substitution between two common residues changes it little. The score therefore encodes the assumption that residue frequencies observed across diverse homologs reflect functional constraint, and it treats columns independently.

## Sources

- B. Reva, Y. Antipin and C. Sander, "Predicting the functional impact of protein mutations: application to cancer genomics", Nucleic Acids Research 39 (2011) e118, Materials and Methods, Equations (1)–(3), <https://doi.org/10.1093/nar/gkr407>, PMCID PMC3177186.
