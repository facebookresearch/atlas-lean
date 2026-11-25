# Gumbel Quantile

For real parameters $\mu$, $\beta$ and $q$, the Gumbel quantile is

$$Q_{\mu,\beta}(q) = \mu - \beta \log(-\log q).$$

The formula is taken literally for all real arguments, with the conventions $\log 0 = 0$ and $\log y = \log\lvert y \rvert$ for $y < 0$. For $\beta \ne 0$ and $0 < q < 1$ it inverts the Gumbel distribution function $F_{\mu,\beta}(x) = \exp(-\exp(-(x - \mu)/\beta))$, and for $\beta > 0$ it is the $q$-quantile of the Gumbel law with location $\mu$ and scale $\beta$.
