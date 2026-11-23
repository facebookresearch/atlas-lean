# Hirschberg recursion step splitting the second sequence

If not both $|x| \le 1$ and $|y| \le 1$, and $|y| \ge |x|$, then for every $n$, $\mathrm{H}_{n+1}(x, y) = \mathrm{H}_n(x_{<k^\ast}, y_{<m})\, \mathrm{H}_n(x_{\ge k^\ast}, y_{\ge m})$ with $m = \lfloor |y|/2 \rfloor$ and $k^\ast$ as in the [reconstruction with fuel](hirschberg-align.md).
