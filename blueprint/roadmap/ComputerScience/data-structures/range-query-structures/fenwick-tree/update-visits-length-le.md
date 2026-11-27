# Logarithmic point-update probe bound

For every natural array length $n$ and
one-indexed input position $i$, the update visits at most $\lfloor\log_2 n\rfloor+1$ entries
when $n>0$. For $i=0$ or $i>n$ the visit list is empty, hence also when $n=0$;
the inequality holds with $\operatorname{log2}(0)=0$.
