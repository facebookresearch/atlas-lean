# Hoorfar–Qi dilogarithm series

Write $L(x) = \sum_{m \ge 1} x^m/m^2 +
\frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on $[0, 1]$ (with $\log 0 = 0$). For
positive integers $p, q$ and real numbers $\theta, \beta$ with $0 < \theta < 1$ and
$0 < \beta < 1$,

$$
\sum_{n \ge 0} L\left(\frac{\beta(1 - \theta^p)(1 - \theta^q)\theta^n}
{(1 - \beta\theta^{n+p})(1 - \beta\theta^{n+q})}\right) =
\sum_{n=0}^{q-1} L\left(\frac{\beta(1 - \theta^p)\theta^n}{1 - \beta\theta^{n+p}}\right) +
\sum_{n=0}^{p-1} L\left(\frac{1 - \theta^q}{1 - \beta\theta^{n+q}}\right) - p\,L(1 - \theta^q).
$$

## Sources

- Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*, INTEGERS 25 (2025), Article A52, Theorem 1, quoting Hoorfar and Qi.
