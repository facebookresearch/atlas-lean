# Probability of a sequence of a given type

Let $n \ge 1$, let $x$ have type $s$ with empirical distribution $P$, and let $Q(a) > 0$ wherever
$P(a) > 0$. Then, with the natural logarithm,

$$Q^n(x) = \prod_a Q(a)^{nP(a)} = \exp\bigl(-n\,[H(P) + D(P \| Q)]\bigr),$$

where $H(P) = \sum_a -P(a)\log P(a)$ and $D(P \| Q) = \sum_a P(a)\log(P(a)/Q(a))$. The identity
is proved for $\prod_a Q(a)^{\mathrm{count}(a,s)}$, which equals $Q^n(x)$ by
[the probability of a sequence depends only on its type](prod-apply-eq-prod-pow.md).

Csiszár states (II.1) for every $Q$, with the conventions $p\log(p/0) = +\infty$ and $e^{-\infty} = 0$.
The support hypothesis excludes exactly that case, where both sides are $0$
([type classes outside the support have probability zero](iid-prob-type-class-eq-zero.md)). The paper allows any base of $\log$ and $\exp$; this page
uses base $e$.

## Background

- [Shannon entropy](../shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md): the entropy there
  is in bits; the natural-log entropy $\sum_a -P(a)\log P(a)$ used here is it times $\log 2$.
- [Kullback–Leibler divergence of finite probability laws](../shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-to-measure.md):
  for probability mass functions the sum $\sum_a P(a)\log(P(a)/Q(a))$ used here is the Kullback–Leibler
  divergence of the associated measures (when $P \ll Q$).

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, equation (II.1).
