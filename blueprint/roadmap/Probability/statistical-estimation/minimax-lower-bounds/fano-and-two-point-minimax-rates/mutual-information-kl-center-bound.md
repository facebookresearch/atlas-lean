# Mutual information is bounded by the average pairwise divergence

Let $V$ be a finite set, $V$ uniform on it, and given $V = v$ let $X$ have law $P_v$ on a finite set, where all supports $\mathrm{supp}\,P_v$ coincide. Then the mutual information (in nats) satisfies

$$
I(X;V) \le \frac{1}{|V|^2}\sum_{v,w} D(P_v \| P_w),
$$

where $D$ is the Kullback-Leibler divergence. In particular $I(X;V) \le \max_{v,w} D(P_v\|P_w)$.

## Proof sketch

Apply the KL-center bound with the uniform prior and center $Q = P_w$, which is admissible because the supports coincide, and average the resulting inequalities over $w$.

## Depends on

- [Mutual information of a finite joint law](../../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/measure-mutual-information-to-measure.md)
- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)
- [KL-center bound on mutual information](../../../../InformationTheory/information-inequalities/kl-tensorization-and-product-conditioning/kl-center-bound-on-mutual-information.md)

## Proof depends on

- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)
- [KL-center bound on mutual information](../../../../InformationTheory/information-inequalities/kl-tensorization-and-product-conditioning/kl-center-bound-on-mutual-information.md)

## Sources

- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
