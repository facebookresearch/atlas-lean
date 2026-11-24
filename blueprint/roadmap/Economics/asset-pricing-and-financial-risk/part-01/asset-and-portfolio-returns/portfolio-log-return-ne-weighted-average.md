# Log returns do not aggregate linearly across assets

The log return of a portfolio is not in general the weighted average of the component log
returns. With equal weights `1/2` and `1/2` on gross returns `2` and `1/2`, the portfolio gross
return is `(1/2) · 2 + (1/2) · (1/2) = 5/4`, whose log return `log (5/4)` is positive, while the
weighted average of the component log returns is `(1/2) log 2 + (1/2) log (1/2) = 0`.
