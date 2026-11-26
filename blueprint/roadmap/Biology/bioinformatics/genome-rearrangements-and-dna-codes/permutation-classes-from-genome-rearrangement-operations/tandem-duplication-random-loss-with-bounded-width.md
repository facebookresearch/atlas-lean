# Tandem duplication–random loss with bounded width

**Model.** A genome is a permutation of $1,\dots,n$. A *tandem duplication–random loss* (duplication-loss) step of width $w$ copies a window of $w$ consecutive genes immediately after itself and then deletes one copy of each duplicated gene, so the window is rearranged into a subsequence of its doubled copy followed by the complementary subsequence. In the bounded-width variant a step costs $1$ if $w\le K$ and $\infty$ otherwise, for a parameter $K\in\mathbb N\cup\{\infty\}$. Let $\mathcal C(K,p)$ be the set of permutations (of any length) obtainable from the identity in at most $p$ steps of width at most $K$.

**Theorem (whole-genome case).** With $K=\infty$ (whole-genome duplication–random loss), a permutation $\sigma\in S_n$ needs exactly

$$\left\lceil \log_2\big(\mathrm{desc}(\sigma)+1\big)\right\rceil$$

steps, where $\mathrm{desc}(\sigma)$ is the number of descents. The permutations obtainable in at most $p$ steps form a pattern-avoiding class whose (finite) basis is the set of pattern-minimal permutations with exactly $2^p$ descents.

**Theorem (one step).** $\mathcal C(K,1)$ is the class of permutations avoiding the $3+2^{K-1}$ patterns $\{321,3142,2143\}\cup D$, where $D$ is the set of permutations of $S_{K+1}$ with exactly one descent that neither start with $1$ nor end with $K+1$.

**Theorem ($p$ steps).** For all $K,p$, $\mathcal C(K,p)$ is a pattern-avoiding class with a finite basis, all of whose patterns have size at most $(Kp+2)^2-2$.

**Theorem (number of steps).** The number of width-$K$ steps needed to obtain a permutation of $S_n$ from the identity is $\Omega\!\big(\log n+n^2/K^2\big)$ in the worst case and on average, and a bucket-sorting scenario achieves $O\!\big(\tfrac nK\log K+\tfrac{n^2}{K^2}\big)$ in the worst case and on average; $K$ may depend on $n$.

## Expansion

A whole-genome step outputs a subsequence of the genome followed by the complementary subsequence, each order-preserving; if the input has $d$ descents the output has at most $2d+1$, so $p$ steps from the identity give at most $2^p-1$ descents, and a merging argument shows this is attained, giving the logarithmic formula. Pattern closure holds because deleting entries from the result of a scenario leaves the result of a scenario of the same length on the pattern. For $p$ steps of width at most $K$, a basis element has a value-position domain (entries not at their own position, together with the positions they cross) of size at most $2Kp+2$; a longer basis element would contain a sorted block of $Kp+1$ fixed points that a scenario can avoid touching, contradicting minimality, which yields the $(Kp+2)^2-2$ bound. Duplication-loss steps are not reversible, so $\mathcal C(K,p)$ is not the class of permutations sortable in $p$ steps.

## Sources

- Mathilde Bouvel, Dominique Rossin, "A variant of the tandem duplication - random loss model of genome rearrangement", arXiv:0801.2524: Section 2.1 (whole-genome theorem and its pattern class), Section 2.2 (one-step basis $\{321,3142,2143\}\cup D$), Section 2.3 (finite basis of size bound $(Kp+2)^2-2$), Section 3 (upper and lower bounds on the number of steps). <https://doi.org/10.48550/arXiv.0801.2524> Published version: Theoretical Computer Science 410, 8-10 (2009), <https://doi.org/10.1016/j.tcs.2008.11.017>.
