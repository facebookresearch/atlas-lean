# Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant

Let $X_0, X_1, \dots$ be independent real random variables on a probability space, each with the
law of $X_0$, and let $F(x) = P(X_0 \le x)$. For every $n$ and every $\varepsilon > 0$, the
empirical distribution function $F_{n+1}(x) = \#\{i \le n : X_i \le x\} / (n + 1)$ of the first
$n + 1$ observations satisfies

$$P\Bigl(\exists x \in \mathbb{R},\ \lvert F_{n+1}(x) - F(x) \rvert > \varepsilon\Bigr) \le 2 \exp\bigl(-2 (n + 1) \varepsilon^2\bigr).$$

No continuity of $F$ is assumed.

This two-sided bound follows from Massart's one-sided Theorem 1 (see Sources) by a union bound
over the two deviations. The upper deviation $\sup_x (F_N - F)$ is bounded with
$\lambda = \sqrt N \varepsilon$. The lower deviation $\sup_x (F - F_N)$ is at most the upper
deviation of the sample $-X_1, \dots, -X_N$ (compare left limits), so it obeys the same bound.
When $\sqrt N \varepsilon < \sqrt{\log 2/2}$ the right-hand side exceeds $1$ and there is
nothing to prove, so the restriction on $\lambda$ in Massart's Theorem 1 costs nothing. The event is $\sup_x \lvert F_{n+1}(x) - F(x) \rvert > \varepsilon$.
The sample size is $N = n + 1$ because the [empirical count](empirical-count.md) counts the indices $0, \dots, n$; with $N$ in place of $n + 1$
this is the usual $P(\lVert F_N - F \rVert_\infty > \varepsilon) \le 2 e^{-2 N \varepsilon^2}$.

Solving $2 e^{-2N\varepsilon^2} = \alpha$ gives the distribution-free confidence band
$F_N(x) \pm \sqrt{\log(2/\alpha) / (2N)}$, which contains the whole of $F$ with probability at
least $1 - \alpha$ for every $F$ and every $N$. Lei, G'Sell,
Rinaldo, Tibshirani and Wasserman use the inequality in this form, $2 \exp(-2 n \varepsilon^2)$, in
the proof of their Theorem 2.4 (arXiv:1604.04173v2, Appendix A.1).

## Related topics

- [Glivenko–Cantelli theorem](glivenko-cantelli.md): the almost sure uniform convergence
  $\lVert F_N - F \rVert_\infty \to 0$. It follows from this inequality by the Borel–Cantelli lemma,
  because $\sum_N 2 e^{-2N\varepsilon^2} < \infty$ for every $\varepsilon > 0$.

## Sources

- Pascal Massart, *The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality*, Ann. Probab. 18
  (1990), no. 3, 1269–1283, DOI 10.1214/aop/1176990746, Theorem 1. As stated on p. 3 of Reeve (below), it gives the one-sided bound
  $P(\sup_x \sqrt N (F_N(x) - F(x)) > \lambda) \le e^{-2\lambda^2}$ for
  $\lambda \ge \min\{\sqrt{\log 2 / 2},\ 1.0841\, N^{-1/6}\}$. Massart's paper could not be
  consulted; the theorem number and statement are taken from Reeve.
- Henry W. J. Reeve, *A short proof of the Dvoretzky–Kiefer–Wolfowitz–Massart inequality*, arXiv:2403.16651v1 (25 March 2024), p. 3 and Corollary 2. Corollary 2 is the one-sided bound $e^{-2\xi^2}$
  (indeed slightly smaller) for every $\xi \ge 0$, for independent $X_1, \dots, X_N$ with an
  arbitrary distribution function $F$. Reeve's paper is the source consulted.
- Aryeh Dvoretzky, Jack Kiefer and Jacob Wolfowitz, *Asymptotic minimax character of the sample
  distribution function and of the classical multinomial estimator*, Ann. Math. Statist. 27 (1956),
  no. 3, 642–669, DOI 10.1214/aoms/1177728174: the inequality with an unspecified constant.
