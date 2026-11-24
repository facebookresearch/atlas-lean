# For weights summing to one, mean strain equals strain of mean voltage

Let $\Omega$ be a finite set of scenarios with real weights $p(\omega)$ summing to one, and let
$V(\omega) \in \mathbb{R}^n$ be the voltage vector of $n$ gauges in scenario $\omega$. For gains
$g_1, \dots, g_n$, all nonzero, and offsets $b_1, \dots, b_n$, the weighted mean of the
[strain vectors](gauge-strain-vec.md) is the strain vector of the weighted mean voltage: for each
channel $i$,

$$
\sum_{\omega} p(\omega)\,\frac{V_i(\omega) - b_i}{g_i} = \frac{\bar V_i - b_i}{g_i},
\qquad \bar V_i = \sum_{\omega} p(\omega)\,V_i(\omega).
$$

The weights may be signed; when they are also nonnegative they form a probability distribution on
the scenarios, and the identity says that the mean strain is the strain of the mean voltage. Total
weight one is used for the offset: for weights of total $s = \sum_{\omega} p(\omega)$ the left side
is $(\bar V_i - s\,b_i)/g_i$.
