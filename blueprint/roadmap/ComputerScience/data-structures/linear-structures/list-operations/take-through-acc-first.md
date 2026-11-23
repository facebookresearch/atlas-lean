# First-witness accumulator gives the inclusive first-hit prefix

Let $v$ map elements to a type $B$, let $p$ be a test that is true or false on $B$, let $w$ map
elements to a type $D$, and let $L$ be a list. Take as accumulators either a value in $D$ or no
value, with the update: an accumulator that has a value keeps it; from no value, an element $x$
gives the value $w(x)$ if $p(v(x))$ is true and no value otherwise. Stop as soon as the
accumulator has a value, starting from no value. The resulting accumulator-stopped prefix of $L$
equals the inclusive first-hit prefix of $L$ for the test $x \mapsto p(v(x))$.
