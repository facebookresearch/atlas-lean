# Hirschberg reconstruction with fuel

Define alignments $\mathrm{H}_n(x, y)$ by recursion on $n$: $\mathrm{H}_0(x, y)$ is empty, and $\mathrm{H}_{n+1}(x, y)$ is

- the [base-case alignment](small-align.md) if $|x| \le 1$ and $|y| \le 1$;
- otherwise, if $|y| \ge |x|$: with $m = \lfloor |y|/2 \rfloor$ and $k^\ast$ the [argmax](best-argmax.md) over $\{0, \dots, |x|\}$ of $k \mapsto \mathrm{NW}(x_{<k}, y_{<m}) + \mathrm{NW}(x_{\ge k}, y_{\ge m})$, the concatenation $\mathrm{H}_n(x_{<k^\ast}, y_{<m})\, \mathrm{H}_n(x_{\ge k^\ast}, y_{\ge m})$;
- otherwise: with $m = \lfloor |x|/2 \rfloor$ and $k^\ast$ the argmax over $\{0, \dots, |y|\}$ of $k \mapsto \mathrm{NW}(x_{<m}, y_{<k}) + \mathrm{NW}(x_{\ge m}, y_{\ge k})$, the concatenation $\mathrm{H}_n(x_{<m}, y_{<k^\ast})\, \mathrm{H}_n(x_{\ge m}, y_{\ge k^\ast})$.
