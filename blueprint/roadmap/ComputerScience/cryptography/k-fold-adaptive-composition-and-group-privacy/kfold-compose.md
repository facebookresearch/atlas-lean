# Adaptive k-fold composition of mechanisms

Let $K_n(t, d)$ be, for each step $n$, each [transcript](transcript.md) $t$ after $n$ steps and each database $d$, a probability mass function on $A_n$. The $k$-fold adaptive composition is the mechanism with values in transcripts after $k$ steps defined by recursion on $k$: for $k = 0$ it is the point mass at the empty transcript; for $k = n + 1$ it draws a transcript $t$ from the $n$-fold composition at $d$, then draws $a \sim K_n(t, d)$, and returns $(t, a)$. Each step sees the earlier outputs and the database.
