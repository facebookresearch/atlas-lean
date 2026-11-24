# Hirschberg recursion step splitting the first sequence

If not both $|x| \le 1$ and $|y| \le 1$, and $|y| < |x|$, then for every $n$, $\mathrm{H}_{n+1}(x, y) = \mathrm{H}_n(x_{<m}, y_{<k^\ast})\, \mathrm{H}_n(x_{\ge m}, y_{\ge k^\ast})$ with $m = \lfloor |x|/2 \rfloor$ and $k^\ast$ as in the [reconstruction with fuel](hirschberg-align.md).
