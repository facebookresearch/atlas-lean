# Randomization tests for segmentation similarity

**Setting.** Let $T$ be a ground-truth segmentation of a sequence of length $N$ with $k$ segments, and let $P$ be a candidate segmentation produced by some segmentation method or biological feature. Similarity is measured by the two [conditional entropies](conditional-entropy-of-segmentations-via-their-union.md) $H(P\mid T)$ and $H(T\mid P)$. The question is whether these values are smaller than what an uninformed segmentation would achieve.

**Null classes.**

- $\mathcal C_{N,k}$: all segmentations of a length-$N$ sequence into exactly $k$ segments; a uniform member is obtained by choosing the $k-1$ interior boundaries uniformly at random (the **$k$-randomization test**).
- $\mathcal C_{N,k,\ell}\subset\mathcal C_{N,k}$: segmentations with $k$ segments whose multiset of segment lengths $\ell$ equals that of $T$; these are the orderings of $T$'s segment lengths, so $|\mathcal C_{N,k,\ell}|\le k!$, with equality when all lengths differ (the **$\ell$-randomization test**).

**Test.** Draw random segmentations $R$ from the chosen class, compute $H(T\mid R)$ and $H(R\mid T)$, and report the empirical fractions

$$p_{T\mid\cdot}=\frac{\#\{R:\ H(T\mid R)<H(T\mid P)\}}{\#R},\qquad p_{\cdot\mid T}=\frac{\#\{R:\ H(R\mid T)<H(P\mid T)\}}{\#R}.$$

$P$ is judged significantly close to $T$ when both fractions are small. The $k$-test asks whether knowing only the number of true segments suffices to match $P$; the $\ell$-test asks whether knowing the true segment-length distribution suffices. The procedure makes no assumption about what a good segmentation looks like and is best suited to candidates with about as many segments as $T$, because otherwise one of the two conditional entropies is large for every $R$.

## Depends on

- [Conditional entropy of segmentations via their union](conditional-entropy-of-segmentations-via-their-union.md)

## Expansion

The construction mirrors label-permutation tests for classifiers: a random member of the null class plays the role of a guess that uses only coarse information about $T$. Because $\mathcal C_{N,k,\ell}\subset\mathcal C_{N,k}$, random segmentations in the $\ell$-class are typically closer to $T$ in the conditional-entropy sense, so passing the $\ell$-test is the stronger evidence. Each conditional entropy costs $O(k)$ by the union formula, so $10^4$ randomizations are cheap.

## Sources

- N. Haiminen, H. Mannila, E. Terzi, "Comparing segmentations by applying randomization techniques", BMC Bioinformatics 8:171 (2007), Methods, subsection "Randomization techniques" (classes $C_{N,k}$ and $C_{N,k,\ell}$, the $k$- and $\ell$-randomization tests), and the result tables reporting $p_k$ and $p_\ell$ over 10,000 randomizations, <https://doi.org/10.1186/1471-2105-8-171>, PMCID: PMC1904250.
