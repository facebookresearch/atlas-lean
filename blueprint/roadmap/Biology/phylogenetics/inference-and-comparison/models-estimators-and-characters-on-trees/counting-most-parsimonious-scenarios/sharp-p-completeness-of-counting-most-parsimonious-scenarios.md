# #P-completeness of counting most parsimonious scenarios

**Setting.** For a multiset $B = \{\nu_1,\dots,\nu_m\}$ of binary strings in $\{0,1\}^n$, an *optimal median* is a string $\mu$ minimizing $\sum_i H(\nu_i,\mu)$, where $H$ is the Hamming distance; let $\mathcal{M}(B)$ be the set of optimal medians. For a nonnegative weight function $f$ define the partition function

$$Z(B, f) = \sum_{\mu \in \mathcal{M}(B)}\ \prod_{i=1}^m f\big(H(\nu_i,\mu)\big).$$

With $f(x) = x!$ it counts **most parsimonious scenarios** on a star tree $K_{1,m}$ whose leaves are labeled by $B$: a median for the center together with an ordering of the $H(\nu_i,\mu)$ mutations on each edge. This is exactly the count for the substitution model of binary sequences, and the count (or an upper bound when adjacencies conflict) for the Single Cut-or-Join (SCJ) model of genome rearrangement, where a genome is encoded by one bit per possible adjacency and the SCJ distance equals the Hamming distance. On a rooted binary tree $T$ with leaf labeling $\varphi$, the analogous count is

$$Z_{T,\varphi}(B, x!) = \sum_{\varphi' \in \mathcal{M}(T,\varphi)}\ \prod_{uv \in E(T)} H\big(\varphi'(u),\varphi'(v)\big)!,$$

summed over most parsimonious labelings $\varphi'$ of all vertices extending $\varphi$.

**Theorem.**

1. Computing $Z(B, x!)$ is #P-complete. Hence counting most parsimonious scenarios on a star tree is #P-complete for the substitution model and for SCJ.
2. Computing $Z_{T,\varphi}(B, x!)$ for an arbitrary binary tree (#BINARY) is #P-complete, so #SPS (small parsimony counting under substitutions) and #SPSCJ (under single cut-or-join) are #P-complete on binary trees.

**Theorem (general weights).** Let $f : \mathbb Z_{\ge0} \to [0,\infty)$ be computable in polynomial time, and let

$$R(n) = \frac{f(n-2)\,f(n+1)^3 f(n+2)^3 f(n+5)}{f(n-1)\,f(n)^3 f(n+3)^3 f(n+4)}.$$

1. If $\log f$ is strictly concave up and either $R(n) > 1$ for all but finitely many $n \ge 2$ (Theorem 6.5, Corollary 6.11) or $R(n) < 1$ for all but finitely many $n \ge 2$ (Theorem 6.12, Corollary 6.13), then counting the medians $\mu$ with $\prod_i f(H(\nu_i,\mu)) \le D$ is #P-complete, and deciding whether $\min_{\mu \in \mathcal M(B)} \prod_i f(H(\nu_i,\mu)) \le D$ is NP-complete.
2. If $\log f$ is strictly concave down and $R(n) \ne 1$ for all but finitely many $n \ge 2$, then counting the medians $\mu$ with $\prod_i f(H(\nu_i,\mu)) \ge D$ is #P-complete, and deciding whether $\max_{\mu \in \mathcal M(B)} \prod_i f(H(\nu_i,\mu)) \ge D$ (some optimal median has product at least $D$) is NP-complete (Corollaries 6.14–6.15). The source's Corollary 6.15 prints $\min$ in this decision problem; this page states $\max$ because the min form is in coNP (a single optimal median with product below $D$ certifies a no-instance), and the max form follows by applying Corollaries 6.11 and 6.13 to $1/f$, as the proof of Corollary 6.14 applies Theorems 6.5 and 6.12 to $1/f$.

For $\log f$ strictly concave down and $R(n)$ eventually $\le 1-\epsilon$ or $\ge 1+\epsilon$, an FPRAS for $Z(B,f)$, or a rapidly mixing Markov chain on medians with stationary distribution proportional to $\prod_i f(H(\nu_i,\mu))$, would imply $\mathrm{RP} = \mathrm{NP}$.

## Expansion

Membership in #P is immediate (guess a median and one ordering per edge). Hardness reduces from #D3SAT, counting satisfying assignments of 3-CNF formulas with distinct variables per clause: each variable $x_i$ is encoded by a pair of coordinates $(x_i, y_i)$ that are *ambiguous* (exactly half the strings carry a $0$), so the medians correspond to truth assignments, and padding coordinates with prescribed numbers of extra ones are added so that, for each clause, the gadget strings give satisfying assignments a larger weight $\prod_i H(\nu_i,\mu)!$ than unsatisfying ones. Prime-number estimates (Rosser–Schoenfeld bounds on the Chebyshev function $\theta(x)$, giving $e^{n/2} \le \prod_{p \le n} p \le e^{3n/2}$ for $n \ge 300$) enter the reduction that recovers the number of satisfying assignments from values of $Z(B,x!)$. The binary-tree result uses an analogous gadget construction on binary trees. The condition on $R(n)$ is what makes the clause gadgets favor (or disfavor) satisfied clauses for general $f$.

## Sources

- István Miklós and Heather Smith, "The computational complexity of calculating partition functions of optimal medians with Hamming distance", arXiv:1506.06107 (2015), Section 1 (partition function and SCJ interpretation), Section 2 (Definitions 2.11–2.12, Lemma 2.13), Section 4 (Corollary 4.3, Theorem 4.4), Section 6 (Theorems 6.5 and 6.12, Corollaries 6.11 and 6.13–6.15), Section 7 (Theorems 7.4–7.7) and Section 9 (Theorem 9.1), <https://doi.org/10.48550/arXiv.1506.06107>. Published version: Advances in Applied Mathematics 102 (2019) 18–82, <https://doi.org/10.1016/j.aam.2018.09.002>.
