# Rademacher complexity of a VC class

Let $n \ge 1$ and let $\mathcal{A}$ be a nonempty family of subsets of the sample $\{1, \dots, n\}$, for example the sets $\{i : h(x_i) = 1\}$ cut out by the hypotheses $h$ of a binary class. Let $d$ be the VC dimension of $\mathcal{A}$, and let $A$ be the set of the $\pm 1$ sign patterns of the members of $\mathcal{A}$. Then

$$R(A) \le \sqrt{\frac{2 \log \sum_{k=0}^{d} \binom{n}{k}}{n}}.$$

Each sign pattern has Euclidean norm $\sqrt{n}$, so Massart's lemma gives $R(A) \le \sqrt{2 \log \lvert \mathcal{A} \rvert / n}$, and the Sauer–Shelah lemma (a family has at most as many members as the family of sets it shatters, which has at most $\sum_{k \le d} \binom{n}{k}$ members) bounds $\lvert \mathcal{A} \rvert$ by $\sum_{k \le d} \binom{n}{k}$. With the [counting bound](../../../../Combinatorics/binomial-coefficients/binomial-sums/bounds-on-partial-sums-of-binomial-coefficients/sum-choose-le-exp-mul-div-pow.md) $\sum_{k \le d} \binom{n}{k} \le (en/d)^d$ this becomes the familiar $O(\sqrt{d \log(n/d) / n})$ rate, [stated explicitly](rademacher-complexity-sign-patterns-le-v.md).

## Informally uses

- [Massart's finite-class lemma](rademacher-complexity-le-of-finite.md): builds on.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Lemma 26.8 and Lemma 6.10 (Sauer–Shelah).
- P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural results*, Journal of Machine Learning Research 3 (2002) 463–482, Theorem 6 (the same $O(\sqrt{d/n})$ phenomenon for the Gaussian complexity, in terms of the empirical VC dimension).
