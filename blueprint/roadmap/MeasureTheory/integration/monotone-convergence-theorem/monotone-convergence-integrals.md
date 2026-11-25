# Monotone convergence theorem

Let $(X, \mathcal{M}, \mu)$ be a measure space and let $f_1, f_2, \ldots \colon X \to [0, \infty]$
be measurable functions with $f_1(x) \le f_2(x) \le \cdots$ for every $x \in X$. Let
$f(x) = \lim_{k \to \infty} f_k(x) = \sup_k f_k(x)$. Then $f$ is measurable and

$$\int f \, d\mu = \lim_{k \to \infty} \int f_k \, d\mu,$$

where the limit exists in $[0, \infty]$.

## Proof

The function $f$ is measurable as the supremum of the measurable functions $f_k$. Since $f_k \le f_{k+1} \le f$,
monotonicity of the integral shows that $\int f_k \, d\mu$ increases to a limit $L \le \int f \, d\mu$. Conversely, let
$\varphi = \sum_{j=1}^m c_j \chi_{A_j} \le f$ with $A_1, \ldots, A_m \in \mathcal{M}$ disjoint and
$c_j \in [0, \infty)$, and let $0 < t < 1$. The sets $E_k = \{x : f_k(x) \ge t \varphi(x)\}$ increase with $k$; each is
measurable, as the union of $X \setminus (A_1 \cup \cdots \cup A_m)$ and the sets $A_j \cap f_k^{-1}([t c_j, \infty])$;
and their union is $X$: if $\varphi(x) = 0$ then $x \in E_1$, and otherwise
$f_k(x) \to f(x) \ge \varphi(x) > t \varphi(x)$. Since $f_k \ge \sum_j t c_j \chi_{A_j \cap E_k}$, the definition of the
integral gives $\int f_k \, d\mu \ge t \sum_j c_j \mu(A_j \cap E_k)$, and continuity of measures from below gives
$\mu(A_j \cap E_k) \to \mu(A_j)$. Hence $L \ge t \sum_j c_j \mu(A_j)$. Letting $t \to 1$ and taking the supremum over
$\varphi$ gives $L \ge \int f \, d\mu$.

## Depends on

- [Lebesgue integral](../nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)
- [Measurable function](../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Measure](../../measures/measures-and-countable-additivity/measures/measure.md)

## Proof depends on

- [Monotonicity of the integral](../nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Continuity of measures from below and from above](../../measures/measures-and-countable-additivity/continuity-of-measures/measure-continuity.md)
- [Suprema of sequences of measurable functions are measurable](../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/i-sup.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 3.11 and 2.53 (version read: the open-access PDF dated 12 June 2026).
