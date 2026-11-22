# Upper bound on the probability of a type class

For $n \ge 1$, an $n$-type with empirical distribution $P$ and any $Q \ge 0$, with the natural
logarithm,

$$Q^n(T_P) \le e^{-nD(P\|Q)}, \qquad D(P\|Q) = \sum_a P(a)\log\frac{P(a)}{Q(a)}.$$

No positivity is assumed on $Q$: if $Q(a) = 0 < P(a)$ for some $a$, the source's divergence is
$+\infty$ and $Q^n(T_P) = 0$, so the inequality holds whatever real value the right side takes (here, with
$x/0 = 0$ and $\log 0 = 0$, such letters contribute $0$ to the sum). This is the right half of (II.5), as in the source.

## Background

- [Kullback–Leibler divergence of finite probability laws](../shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-to-measure.md):
  for probability mass functions the sum $\sum_a P(a)\log(P(a)/Q(a))$ used here is the Kullback–Leibler
  divergence of the associated measures (when $P \ll Q$).

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Lemma II.2, (II.5).
- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Lemma 2.3 (base 2).
