# Solutions of systems of type equations

Consider a system of equations $t_i = \gamma_i[t_1, \dots, t_n]$, $i = 1, \dots, n$, between [recursive types](recursive-types-and-their-tree-expansions.md), and write $\vdash \alpha = \beta$ for
derivability from reflexivity, symmetry, transitivity, congruence for $\to$ and $\mu$, the axioms $\mu t.\, t = \bot$ and $[\mu t.\, \alpha / t]\alpha = \mu t.\, \alpha$
(fold–unfold), and the contraction rule: from $[\beta/t]\alpha = \beta$ and $[\beta'/t]\alpha = \beta'$ with $\alpha$ contractive in $t$, infer $\beta = \beta'$. Here $\alpha$ is
*contractive* in $t$ if $t$ does not occur free in $\alpha$, or $\alpha$ can be rewritten by unfolding to the shape $\alpha_1 \to \alpha_2$.

1. (existence) The system has a solution up to fold–unfold: there are types $\alpha_1, \dots, \alpha_n$ with $\vdash \alpha_i = \gamma_i[\alpha_1, \dots, \alpha_n]$, obtained by iterated
   elimination, starting from $\mu t_n.\, \gamma_n$.
2. (uniqueness) If every $\gamma_i$ is contractive in every $t_j$, and both $\alpha_1, \dots, \alpha_n$ and $\beta_1, \dots, \beta_n$ are solutions, then $\vdash \alpha_i = \beta_i$ for every $i$; the proof
   uses the contraction rule. Ruling out bare variables is not enough: $t = \mu s.\, t$ has the solutions $\bot$ and $\top$, whose trees differ.

These are the steps from which [completeness of these rules](complete-rules-for-recursive-type-equality.md) is derived: two types with the same tree expansion are both
solutions of one system whose right-hand sides are node contexts $p[t_1, \dots, t_n]$, which are contractive in every variable.

## Depends on

- [Recursive types and their tree expansions](recursive-types-and-their-tree-expansions.md)

## Sources

- R. M. Amadio and L. Cardelli, "Subtyping recursive types", *ACM Transactions on Programming Languages and Systems* 15(4):575–631, 1993, <http://lucacardelli.name/Papers/SRT.pdf>: Section 5.1 (contractiveness), Section 5.2, Lemmas 5.2.1 and 5.2.2, Definition 5.2.3 and the remark after it (node contexts are contractive), and the use of Lemmas 5.2.5–5.2.6 in Theorem 5.2.7.
