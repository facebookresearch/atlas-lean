# Running on a random tape with a transcript

For queries in $X$, answers in $Y$ and an answer rule $h(x, r)$, running an oracle computation on a
tape $(r_1, r_2, \dots)$ with a transcript gives its output together with the list of its (query,
answer) pairs, where the $i$-th query $x$ is answered by $h(x, r_i)$, using a fixed default entry in
place of $r_i$ once the tape is used up.
