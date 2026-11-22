# Backward search for a compression collision

Let $h : S \times B \to S$ be a compression
function with initial value $iv$, and for a list of blocks written last block first let $z(xs)$
be its chaining value: $z([\,]) = iv$ and $z(x :: xs) = h(z(xs), x)$. Given two such lists, the
search compares their leading compression inputs: on $x :: xs$ and $y :: ys$, if
$(z(xs), x) = (z(ys), y)$ it continues with $xs$ and $ys$, and otherwise it returns the pair
$((z(xs), x), (z(ys), y))$. When either list is empty it returns no pair.
