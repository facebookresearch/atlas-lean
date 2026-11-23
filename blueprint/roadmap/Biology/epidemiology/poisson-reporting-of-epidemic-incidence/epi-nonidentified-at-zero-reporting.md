# Nonidentification at zero reporting

Compose the
reporting law with the intensity map at `rho = 0`. The resulting
law family is constant in the epidemic incidence vector (every
incidence has the same background-only intensity, by
`intensityAt_zero`), while the estimand `incidence 0` varies: the
zero vector and the vector differing only at coordinate `0` have
the same reporting law but estimands `0` and `1`. Hence the
estimand is not identified by the zero-reporting law.
