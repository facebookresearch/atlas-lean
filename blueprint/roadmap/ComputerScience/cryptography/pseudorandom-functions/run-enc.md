# Running an algorithm against the bounded encryption oracle

Let $X$ be a set, $Y$ an
abelian group written additively, $f : X \to Y$ a function, $q \in \mathbb{N}$ and
$\rho : \{0, \dots, q - 1\} \to X$ the encryption randomness of the queries. Run from query index
$i \in \mathbb{N}$, an oracle algorithm with messages in $Y$ as queries, answers in $X \times Y$
and outputs in $\beta$ either fails or yields its output together with the next query index: if
it stops with output $a$, the result is $(a, i)$; if it queries a message $m$ and $i < q$, the
oracle answers $(\rho(i), f(\rho(i)) + m)$ and the run continues from index $i + 1$; if it
queries a message and $i \ge q$, the run fails.
