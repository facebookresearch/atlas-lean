# Top-k answer

Let $f$ assign to each object a score in a linearly ordered set, and let
$k \in \mathbb{N}$. A finite set $Y$ of objects is a top-$k$ answer for $f$ when it has exactly
$k$ elements and $f(z) \le f(y)$ for every $y \in Y$ and every object $z \notin Y$. Objects with
equal scores may fall on either side of $Y$: no tie-breaking order is fixed, and there may be
several top-$k$ answers.
