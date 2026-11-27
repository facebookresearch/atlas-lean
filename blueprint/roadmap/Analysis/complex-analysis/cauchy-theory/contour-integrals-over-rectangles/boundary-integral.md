# Boundary integral over a rectangle

Let $E$ be a complex Banach space and let $R$ be a
rectilinear rectangle with first corner $z$ and second corner $w$. The boundary integral of a
function $f : \mathbb{C} \to E$ over $R$ is

$$\int_{\operatorname{Re} z}^{\operatorname{Re} w} f(x + i \operatorname{Im} z)\,dx -
\int_{\operatorname{Re} z}^{\operatorname{Re} w} f(x + i \operatorname{Im} w)\,dx +
i \int_{\operatorname{Im} z}^{\operatorname{Im} w} f(\operatorname{Re} w + iy)\,dy -
i \int_{\operatorname{Im} z}^{\operatorname{Im} w} f(\operatorname{Re} z + iy)\,dy,$$

where each integral is an oriented Bochner interval integral, so $\int_a^b = -\int_b^a$.

The corner order determines the sign; when $\operatorname{Re} z \le \operatorname{Re} w$ and
$\operatorname{Im} z \le \operatorname{Im} w$ this is the integral of $f$ over the positively
oriented boundary of the rectangle.
