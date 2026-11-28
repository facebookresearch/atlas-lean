# Running against a lazy table with presampled answers

Let $c$ be an adaptive oracle
algorithm with queries in $P$, answers in $\alpha$ and output in $\beta$, let
$t : \{0, \dots, Q - 1\} \to \alpha$ be a tape of answers and let $d \in \beta$ be a default
output. Started at query counter $n$ with a table $T_0$ of recorded answers (a partial function
$P \rightharpoonup \alpha$), the run keeps a current table $T$, at first $T_0$, and answers the
query $p$ asked when the counter is $m$ as follows: if $T$ records an answer $a$ for $p$, the
answer is $a$; otherwise, if $m < Q$, the answer is $t(m)$, and $T$ then records $t(m)$ for $p$;
otherwise the run stops with output $d$. The counter goes up by one at every query. The result is
the output of $c$, or $d$ if the run stops.
