# TreeBH controls the selective false discovery rate at every level

Use the setting and notation of [the selective false discovery rate and TreeBH](selective-fdr-and-the-treebh-procedure.md), which runs the [Benjamini–Hochberg procedure](../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md) in each selected family. Consider the assumptions:

- (A1) the vector of $p$-values at the finest level $L$ is positive regression dependent on the subset of true null hypotheses;
- (A3) each parent $p$-value is $P_i = f_i(P_{\mathcal{F}_i})$ for a coordinatewise nondecreasing combination function $f_i$ of the $p$-values of the family it indexes;
- (A4) each hypothesis at level $\ell \le L - 1$ is the intersection of its children.

A hierarchical procedure is **consonant** if whenever a parent hypothesis is rejected, at least one hypothesis in the family it indexes is rejected.

**Statement.**

1. For a consonant hierarchical testing procedure, $\mathrm{sFDR}_{\ell-1} \le \mathrm{sFDR}_\ell$ for every $\ell \ge 1$, with equality when every level-$\ell$ family consists entirely of true nulls or entirely of false nulls.
2. If parent $p$-values are computed by Simes' rule from their children and $q^{(0)} \le q^{(1)} \le \dots \le q^{(L)}$, TreeBH is consonant.
3. Under (A1) and (A3), TreeBH guarantees $\mathrm{sFDR}_L \le q^{(L)}$.
4. Under (A1), (A4) and (A3) with Simes' rule, and equal targets $q^{(0)} = \dots = q^{(L)} = q$, TreeBH guarantees $\mathrm{sFDR}_\ell \le q$ for every $\ell \in \{0, \dots, L\}$; the bound is attained when all nulls are true with independent uniform $p$-values.

## Depends on

- [Selective false discovery rate and the TreeBH procedure](selective-fdr-and-the-treebh-procedure.md)
- [Benjamini–Hochberg rejection set](../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)

## Expansion

Part 4 follows from parts 1–3: part 3 bounds the finest level, part 2 gives consonance, and part 1 propagates the bound to coarser levels. Consonance makes the error of a rejected parent an average over a nonempty set of rejected children, so the level-$(\ell-1)$ error indicator is dominated by the averaged level-$\ell$ errors. The paper also proves a generalized version in which each selected family is tested by any simple selection rule controlling an error rate $\mathbb{E}(\mathcal{C}_i)$, under independence across finest-level families.

## Sources

- M. Bogomolov, C. B. Peterson, Y. Benjamini and C. Sabatti, "Hypotheses on a tree: new error rates and testing strategies", Biometrika 108 (2021), 575–590, <https://doi.org/10.1093/biomet/asaa086> (PMC9945647), section 4.2, Definition 1, Assumptions 1–4, Proposition 1, Lemma 1 and Theorem 1.
