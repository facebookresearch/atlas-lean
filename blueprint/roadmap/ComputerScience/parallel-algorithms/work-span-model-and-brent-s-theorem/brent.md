# Brent's theorem with the work and span laws

Let $G$ be a computation DAG on $n$
unit-time tasks with span $D$, and let $p \ge 1$. Then some schedule of $G$ on $p$ processors
has length $T$ with $pT \le n + (p - 1)D$, and every schedule of $G$ on $p$ processors has a
length $T'$ with $n \le pT'$ (the work law) and $D \le T'$ (the span law).
