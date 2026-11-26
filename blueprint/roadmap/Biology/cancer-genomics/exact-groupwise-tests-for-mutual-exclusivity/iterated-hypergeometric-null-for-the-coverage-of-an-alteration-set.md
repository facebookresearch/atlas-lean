# Iterated hypergeometric null for the coverage of an alteration set

**Setting.** Let $\mathbf{A} = (a_{ij})$ be the $m\times n$ binary matrix with $a_{ij} = 1$ when alteration $i$ (a functional SNV, amplification or deletion of a gene) is present in tumour sample $j$. Alteration $i$ has coverage $\Gamma(i) = \sum_j a_{ij}$. For an alteration set $M = \{g_1,\dots,g_{|M|}\}$, the coverage is

$$\Gamma(M) = \Big|\Big\{j : \sum_{g\in M}a_{gj}\ge 1\Big\}\Big|,$$

and the overlap is $\Gamma(M)$ subtracted from $\sum_{g\in M}\Gamma(g)$. $M$ is perfectly mutually exclusive iff its overlap is $0$. Alterations that hit the same pathway confer no extra advantage when combined, so selection makes them **anti-co-occur**.

**Test.** Test $H_0$, that the alterations in $M$ occur independently across samples, against $H_1$, that they co-occur less often than under independence. Use the statistic $\Gamma(M)$, large under $H_1$, conditioned on the marginal coverages $\mathbf{C} = (\Gamma(1),\dots,\Gamma(m))$.

**Proposition.** Let $M^{(s)} = \{g_1,\dots,g_s\}$. Under $H_0$, conditionally on the coverages,

$$\Gamma(M^{(s)}) \,\big|\, \big(\Gamma(M^{(s-1)}),\Gamma(g_s)\big) \ \sim\ \Gamma(M^{(s-1)}) + \operatorname{Hyp}\big(n,\ n - \Gamma(M^{(s-1)}),\ \Gamma(g_s)\big),$$

where $\operatorname{Hyp}(n,k,r)$ has mass $\binom{k}{x}\binom{n-k}{r-x}/\binom{n}{r}$. Hence the exact conditional law of $\Gamma(M)$ is the iterated convolution

$$f_{\Gamma(M^{(s)})\mid\mathbf{C}}(x) = \sum_y f_{\operatorname{Hyp}(n,n-y,\Gamma(g_s))}(x-y)\,f_{\Gamma(M^{(s-1)})\mid\mathbf{C}}(y),$$

and the exact p-value $p_M = \sum_{x\ge\Gamma(M)} f_{\Gamma(M)\mid\mathbf{C}}(x)$ costs $|M|-2$ convolutions, which is linear in $|M|$. For $|M| = 2$ this is the one-sided Fisher exact test. For a perfectly mutually exclusive set each sum has a single term. The test asks whether the union of $|M|$ random subsets of $[n]$ with the observed sizes is larger than expected by chance.

**Combining tumour types.** Type-specific mutation frequencies alone can create spurious anti-co-occurrence. Per-type p-values $p_\tau$ are therefore combined by Stouffer's method,

$$p = \Phi\Big(\sum_\tau v_\tau\Phi^{-1}(p_\tau)\big/\big(\textstyle\sum_\tau v_\tau^2\big)^{1/2}\Big).$$

For pairs, $v_\tau$ is the inverse null standard deviation of the empirical log-odds ratio. For larger sets, $v_{M,\tau}$ is the root sum of squares of the pairwise weights. To keep the combined test exact despite the discrete statistics, the p-values are randomized: $p^{\rm rand}_\tau = p_\tau - (p_\tau - p^-_\tau)U$ with $U$ uniform, which gives $\Pr(p\le\alpha) = \alpha$.

## Expansion

Under $H_0$ with fixed coverages, the samples carrying $g_s$ form a uniformly random $\Gamma(g_s)$-subset of $[n]$, independent of the other alterations. The number of them that fall outside the current union, of size $\Gamma(M^{(s-1)})$, is hypergeometric, and the union grows by exactly that number. This gives the recursion. A weighted multiple-testing correction then upweights small alteration sets. Its Lemma 1 bounds by $\alpha$ the null probability that some one-gene extension $M\cup\{g\}$ has a smaller weighted p-value than $M$. Candidate sets come from a greedy search, and the method is applied to TCGA pan-cancer data with 1,418 alterations across 5,807 samples from 22 cancer types.

## Sources

- P. Ginzberg, F. Giorgi and A. Califano, "Searching for Gene Sets with Mutually Exclusive Mutations", arXiv:1609.05564 (2016), Sections 2–4 (exact groupwise test, Stouffer combination, weighted correction and Lemma 1), <https://doi.org/10.48550/arXiv.1609.05564>.
