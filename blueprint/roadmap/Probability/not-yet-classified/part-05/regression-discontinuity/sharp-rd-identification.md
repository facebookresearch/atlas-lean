# Identification in the sharp regression-discontinuity design

**Identification in the sharp regression-discontinuity design** (Hahn, Todd and van der
Klaauw 2001; Imbens and Lemieux 2008, §2.2): treatment is `1{X ≥ c}`; `m_d` is a version of
`x ↦ E[Y(d) | X = x]`, continuous at `c`; units are observed arbitrarily close to `c` on both
sides (every one-sided neighborhood `(c, c + ε)`, `(c - ε, c)` has positive probability under
the law of `X`). Then for *any* version `r` of `x ↦ E[Y | X = x]` (`Y` the observed outcome)
that has one-sided limits at `c`, the jump `lim_{x↓c} r x - lim_{x↑c} r x` equals the cutoff
effect `m₁ c - m₀ c = E[Y(1) - Y(0) | X = c]`.
