# Ternary dot product distribution

**Setting.** Let $T$ be a finite ground set (the transcripts of a signed causal graph). A *ternary classification* of $T$ is a map $C : T \to \{-1, 0, 1\}$ (downregulated, unchanged, upregulated), represented by a vector $u(C) \in \{-1, 0, 1\}^{T}$. The agreement of two classifications is the dot product $u(C) \cdot u(C')$. Fix an experimental classification $C$ with $q_\sigma = \#\{t : C(t) = \sigma\}$ and a predicted classification $C'$ with $n_\sigma = \#\{t : C'(t) = \sigma\}$, $\sigma \in \{-, 0, +\}$. A *randomization* of $C'$ is any classification with the same counts $(n_+, n_-, n_0)$, chosen uniformly among the

$$D_{\mathrm{tot}} = \binom{|T|}{n_+,\ n_-,\ n_0}$$

possibilities. The **ternary dot product distribution** is the law of $u(C) \cdot u(C_R')$ for a uniform randomization $C_R'$.

**Statement** (Chindelevitch et al. 2012, Results, "Ternary Dot Product Distribution"). Let $n_{\sigma\tau}$ be the number of elements with $C = \sigma$ and $C_R' = \tau$. The $3 \times 3$ contingency table $(n_{\sigma\tau})$ has row sums $q_\sigma$ and column sums $n_\tau$, so it is determined by its corner $(n_{++}, n_{+-}, n_{-+}, n_{--})$. The number of randomizations producing a given corner is

$$D[n_{\pm\pm}] = \binom{q_+}{n_{++},\ n_{+-},\ n_{+0}} \binom{q_-}{n_{-+},\ n_{--},\ n_{-0}} \binom{q_0}{n_{0+},\ n_{0-},\ n_{00}},$$

the score of such a randomization is $S = n_{++} + n_{--} - n_{+-} - n_{-+}$, and

$$\Pr(S = s) = \frac{1}{D_{\mathrm{tot}}} \sum_{n_{\pm\pm} :\ S[n_{\pm\pm}] = s} D[n_{\pm\pm}],$$

with the $p$-value of an observed score given by the right tail. Summing each $D$ value directly costs $O(N^4)$ with $N = \max(n_+, n_-, q_+, q_-)$; grouping the terms with fixed $n_{++} + n_{--}$ and fixed $n_{+-} + n_{-+}$ gives sums of products of three binomial coefficients that satisfy a three-term linear recurrence (found by the WZ method), which yields an $O(N^3)$ algorithm.

## Proof depends on

- [Words of given content are counted by the multinomial coefficient](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/card-words-of-content-eq-multinomial.md)
- [Marked items in a uniform random sample](../../../../Probability/distributions/discrete/hypergeometric-distribution/marked-items-in-a-uniform-random-sample.md)
- [The Fisher exact p-value as a hypergeometric tail sum](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue-eq-sum.md)

## Proof sketch

The multinomial formula counts, row by row, the ways to choose which of the $q_\sigma$ elements with experimental label $\sigma$ receive each predicted label; the three rows are independent once the column counts are fixed by the corner. If neither classification uses the label $0$ ($q_0 = n_0 = 0$), then $n_{+-} = q_+ - n_{++}$, $n_{-+} = n_+ - n_{++}$ and $n_{--} = q_- - n_+ + n_{++}$, so $S = 4 n_{++} + q_- - q_+ - 2 n_+$ is an affine function of $n_{++}$, and $n_{++}$ is hypergeometric with population $|T|$, $q_+$ marked elements and $n_+$ draws: the test reduces to Fisher's exact test on a $2 \times 2$ table. The distribution is thus a three-valued generalization of Fisher's exact test, in which agreements and disagreements of sign contribute with opposite signs and unchanged elements contribute nothing.

## Sources

- L. Chindelevitch, P.-R. Loh, A. Enayetallah, B. Berger and D. Ziemek, "Assessing statistical significance in causal graphs", BMC Bioinformatics 13 (2012), 35, Results ("Ternary Dot Product Distribution": problem definition, Table 2, algorithm) and Methods, <https://doi.org/10.1186/1471-2105-13-35>, PMCID PMC3307026.
