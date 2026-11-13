# Winning the forgery game

A forger $c$, an adaptive oracle algorithm with queries in $M$,
answers in $T$ and output in $M \times T$, wins against the tagging oracle $O \colon M \to T$
when, run with oracle $O$, it outputs a pair $(m, t)$ with $O(m) = t$ and $m$ is not among the
queries it asks in that run.
