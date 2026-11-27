# Kendall's geometric tail ratio

For real numbers $b, d, t$ put $E = e^{(b - d) t}$ and define

$$\beta(t) = \frac{b\,(E - 1)}{b E - d} \quad \text{if } b \ne d, \qquad \beta(t) = \frac{b t}{1 + b t} \quad \text{if } b = d,$$

where a quotient with zero denominator is read as $0$. For $b, d \ge 0$ and $t \ge 0$ it is the
ratio of the geometric tail of [Kendall's law](prob.md) of the linear birth–death process at time
$t$:
$P(X_t = n + 1) = (1 - \alpha(t))(1 - \beta(t))\, \beta(t)^n$.

## Sources

- D. G. Kendall, *On the generalized "birth-and-death" process*, Annals of Mathematical
  Statistics 19 (1948), 1–15.
