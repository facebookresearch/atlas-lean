# First-witness fold over the inclusive first-hit prefix

Let $v$ map elements to a type $B$, let $p$ be a test that is true or false on $B$, let $w$ map
elements to a type $D$, and let $L$ be a list. Consider the update on accumulators that are either
a value in $D$ or no value: an accumulator that has a value keeps it; from no value, an element
$x$ gives the value $w(x)$ if $p(v(x))$ is true and no value otherwise. Folding this update from
the left, starting from no value, over the inclusive first-hit prefix of $L$ for the test
$x \mapsto p(v(x))$ gives $w(x)$ for the first element $x$ of $L$ with $p(v(x))$ true, and no value
if there is no such element.
