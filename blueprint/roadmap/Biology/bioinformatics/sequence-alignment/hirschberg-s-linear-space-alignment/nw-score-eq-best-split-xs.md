# Hirschberg split identity, splitting the first sequence

For all sequences $x, y$ and $m \le |x|$, let $k^\ast$ be the [argmax](best-argmax.md) over $\{0, \dots, |y|\}$ of $k \mapsto \mathrm{NW}(x_{<m}, y_{<k}) + \mathrm{NW}(x_{\ge m}, y_{\ge k})$. Then $\mathrm{NW}(x_{<m}, y_{<k^\ast}) + \mathrm{NW}(x_{\ge m}, y_{\ge k^\ast}) = \mathrm{NW}(x, y)$.
