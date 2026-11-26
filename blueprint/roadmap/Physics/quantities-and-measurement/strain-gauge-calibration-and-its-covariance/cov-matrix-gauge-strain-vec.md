# Strain covariance from voltage covariance, for weights summing to one

Let $\Omega$ be a finite set of scenarios with real weights $p(\omega)$ summing to one, and let
$V(\omega) \in \mathbb{R}^n$ be the voltage vector of $n$ gauges in scenario $\omega$. Write
$E_p X = \sum_{\omega} p(\omega)\,X(\omega)$ for the weighted mean and $C_V$ for the weighted
covariance matrix of the voltages, $C_V(i, j) = E_p[(V_i - E_p V_i)(V_j - E_p V_j)]$. For gains
$g_1, \dots, g_n$, all nonzero, and offsets $b$, the weighted covariance matrix $C_\varepsilon$ of
the [strain vectors](gauge-strain-vec.md) $\varepsilon(\omega)$ is

$$
C_\varepsilon = D\,C_V\,D^{\mathsf T}, \qquad D = \operatorname{diag}(1/g_1, \dots, 1/g_n).
$$

The offsets do not enter, and since $D^{\mathsf T} = D$ the entries are
$C_\varepsilon(i, j) = C_V(i, j)/(g_i\,g_j)$
([entrywise form](cov-matrix-gauge-strain-vec-apply.md)). The weights may be signed; when they are
also nonnegative, $C_V$ and $C_\varepsilon$ are the covariance matrices of the voltage and strain
vectors under the probability distribution $p$ on the scenarios.
