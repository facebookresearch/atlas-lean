# Storing tape entries or their images

Let $g : \gamma \to \alpha$, let
$t : \{0, \dots, Q - 1\} \to \gamma$ be a tape and $T$ a table with values in $\gamma$, and let
$c$ be an adaptive oracle algorithm with queries in $P$ and answers in $\alpha$. Running $c$
against the lazy table with presampled answers $g \circ t$, started with the table that records
$g(a)$ wherever $T$ records $a$, gives the same result as running, against the lazy table with
presampled answers $t$ started with $T$, the algorithm that runs $c$ and hands it $g(z)$ for each
answer $z$, at the same counter and with the same default output.
