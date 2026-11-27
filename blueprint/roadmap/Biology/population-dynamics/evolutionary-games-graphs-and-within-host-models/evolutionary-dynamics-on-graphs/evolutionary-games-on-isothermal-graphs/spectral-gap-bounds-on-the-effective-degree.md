# Spectral gap bounds on the effective degree

Consider a family of connected isothermal graphs whose sizes tend to infinity and whose spectral
gap (the difference between the two largest eigenvalues of the weighted adjacency matrix) tends to
a limit $g$ with $0 < g \le 1$; such a family is a family of isothermal expander graphs. Assume
that the Simpson-degree distributions converge, pointwise in their quantile functions, to a
continuous function $\kappa(x)$ on $[0,1]$ (a fraction $x$ of the limiting Simpson degrees are at most
$\kappa(x)$). For $0 \le a < b \le 1$ let
$\kappa_{[a,b]} = \bigl((b-a)^{-1}\int_a^b \kappa(x)^{-1}\,dx\bigr)^{-1}$ denote the harmonic mean of the
limiting Simpson degrees lying between the $a$th and $b$th quantiles, and write
$\kappa_{\mathrm{H}} = \kappa_{[0,1]}$ for their harmonic mean and
$\kappa_{\mathrm{A}} = \int_0^1 \kappa(x)\,dx$ for their arithmetic mean. Then the remeeting times satisfy $\tau_i \le N/g$
asymptotically for every vertex $i$, and the effective degree obeys the asymptotic bounds

$$\kappa_{[0,g]} \ \le\ \tilde{\kappa} \ \le\ \kappa_{[1-g,\,1]},$$

hence also the looser bounds

$$g\,\kappa_{\mathrm{H}} \ \le\ \tilde{\kappa} \ \le\ \frac{\kappa_{\mathrm{A}}}{g}.$$

As $g \to 1$ both quantile bounds converge to $\kappa_{\mathrm{H}}$.

## Depends on

- [Simpson degree and effective degree of an isothermal graph](simpson-degree-and-effective-degree.md)

## Remarks

Because a harmonic mean is dominated by its smallest entries, a graph may contain high-degree hubs,
even enough to make the arithmetic average degree diverge, and still have a small effective degree
and therefore strong support for cooperation. For a limiting Simpson-degree density
$f(\kappa) \propto \kappa^{-\gamma}$ on $[\kappa_0, \infty)$ with $\gamma \ge 2$, evaluating the
quantile bounds at the quantile function $\kappa(x) = \kappa_0 (1-x)^{-1/(\gamma-1)}$ gives
$\tilde{\kappa} \le \bigl(\gamma/(\gamma-1)\bigr) \kappa_0 g^{-1/(\gamma-1)}$, which stays
finite even at $\gamma = 2$, where the arithmetic mean diverges.

## Sources

- B. Allen, G. Lippner, M. A. Nowak, "Evolutionary games on isothermal graphs",
  Nature Communications 10 (2019) 5107, Eqs. (6)-(8),
  <https://doi.org/10.1038/s41467-019-13006-7> (PMC6841731).
