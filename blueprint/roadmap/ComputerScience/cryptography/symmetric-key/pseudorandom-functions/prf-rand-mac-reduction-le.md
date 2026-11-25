# Forging against a random function

Let $M$ and $T$ be finite sets with $T$ nonempty, and
let $A$ be a forger: an oracle algorithm with coins in a finite nonempty set that queries tags
in $T$ of messages in $M$ and outputs a message together with a tag. When the tagging oracle is
a uniformly random function $M \to T$ and the coins are uniform, the MAC reduction built from
$A$ accepts (that is, $A$ outputs the correct tag of a message it never queried) with
probability at most $1/|T|$.
