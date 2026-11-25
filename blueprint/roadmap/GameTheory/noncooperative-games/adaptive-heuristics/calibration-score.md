# Calibration score

For binary outcomes $x_s$ and forecasts $f_s \in \{0, 1/k, \dots, 1\}$, with $k \ge 1$, over $t \ge 1$
rounds, let
$n(p)$ be the number of rounds with forecast $p$ and $\rho(p)$ the fraction of them with outcome
$1$. The calibration score is

$$C_t = \sum_{p} \bigl(\rho(p) - p\bigr)^2 \frac{n(p)}{t} .$$

## Sources

- D. P. Foster and R. V. Vohra, "Asymptotic calibration", Biometrika 85(2) (1998), 379–390, §2.
