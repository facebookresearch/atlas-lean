# Perceptron training

Given a finite list $D$ of labelled examples, a number $n$ of passes
and weights $w$, training returns nothing when $n = 0$. When $n = m + 1$, it runs one perceptron
pass over $D$ from $w$ with mistake count $0$; if that pass makes no mistake it returns $w$, and
otherwise it trains on $D$ for $m$ passes from the weights the pass produced. So training repeats
passes until one makes no mistake, for at most $n$ passes, and returns the weights of that pass,
or nothing if every pass made a mistake.
