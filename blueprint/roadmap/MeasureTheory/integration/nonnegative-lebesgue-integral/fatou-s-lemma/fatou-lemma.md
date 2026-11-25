# Fatou's lemma

Let $(X, \mathcal{M}, \mu)$ be a measure space and let $f_1, f_2, \ldots \colon X \to [0, \infty]$
be measurable functions. Define $f \colon X \to [0, \infty]$ by $f(x) = \liminf_{k \to \infty} f_k(x)$. Then $f$ is
measurable and

$$\int f \, d\mu \le \liminf_{k \to \infty} \int f_k \, d\mu.$$

## Proof

Let $g_k = \inf_{j \ge k} f_j$. Each $g_k$ is measurable as the infimum of the measurable functions $f_j$, $j \ge k$,
and $g_1 \le g_2 \le \cdots$ with $\sup_k g_k = f$. By the monotone convergence theorem, $f$ is measurable and
$\int f \, d\mu = \lim_k \int g_k \, d\mu$. For $j \ge k$ we have $g_k \le f_j$, so
$\int g_k \, d\mu \le \inf_{j \ge k} \int f_j \, d\mu$ by monotonicity of the integral. Hence
$\int f \, d\mu \le \lim_k \inf_{j \ge k} \int f_j \, d\mu = \liminf_k \int f_k \, d\mu$.

## Depends on

- [Lebesgue integral](../lebesgue-integral/lebesgue-integral.md)
- [Measurable function](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Measure](../../../measures/measures-and-countable-additivity/measures/measure.md)

## Proof depends on

- [Monotone convergence theorem](../../monotone-convergence-theorem/monotone-convergence-integrals.md)
- [Monotonicity of the integral](../lebesgue-integral/lintegral-mono.md)
- [Infima of sequences of measurable functions are measurable](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/i-inf.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Exercise 17 in Section 3A (version read: the open-access PDF dated 12 June 2026).
