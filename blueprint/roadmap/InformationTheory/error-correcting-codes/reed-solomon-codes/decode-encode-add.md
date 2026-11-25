# Berlekamp-Welch corrects every error of weight at most $\lfloor (n-k)/2 \rfloor$

Let
$F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct, let $k \le n$,
put $t = \lfloor (n-k)/2 \rfloor$, and let $S$ be a solver for the key equations with error
budget $t$. For every polynomial $p \in F[X]$ of degree less than $k$ and every error word
$\varepsilon \in F^n$ with at most $t$ nonzero entries, the Berlekamp-Welch decoder with
solver $S$, run on the received word
$(p(\alpha_0) + \varepsilon_0, \dots, p(\alpha_{n-1}) + \varepsilon_{n-1})$, returns $p$.
