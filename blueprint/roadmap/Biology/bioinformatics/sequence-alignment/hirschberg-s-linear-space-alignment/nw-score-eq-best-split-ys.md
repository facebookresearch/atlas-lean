# Hirschberg split identity, splitting the second sequence

For all sequences $x, y$ and $m \le |y|$, let $k^\ast$ be the [argmax](best-argmax.md) over $\{0, \dots, |x|\}$ of $k \mapsto \mathrm{NW}(x_{<k}, y_{<m}) + \mathrm{NW}(x_{\ge k}, y_{\ge m})$. Then

$$\mathrm{NW}(x_{<k^\ast}, y_{<m}) + \mathrm{NW}(x_{\ge k^\ast}, y_{\ge m}) = \mathrm{NW}(x, y),$$

with the notation of [the split bound](split-score-le-nw-score-ys.md).
