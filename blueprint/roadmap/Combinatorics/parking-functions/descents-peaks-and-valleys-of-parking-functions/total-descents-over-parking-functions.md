# Total number of descents over parking functions

Let $n$ be a natural number. A descent of
a function $f \colon \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is an index $i$ with $i + 1 < n$
and $f(i) > f(i+1)$. Summed over all parking functions
$f \colon \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ of length $n$, the number of descents is
$\binom{n}{2} (n+1)^{n-2}$, which is $0$ for $n < 2$.

Parking functions are taken in threshold form: for each $k < n$, at most $n - k$ of the values
$f(i)$ are at least $k$. This is equivalent to the source's sorted-preference formulation.

## Sources

- Paul R. F. Schumacher, "Descents in Parking Functions," Journal of Integer Sequences 21 (2018), Article 18.2.3, Theorem (label `thm:descount`), line 180, https://cs.uwaterloo.ca/journals/JIS/VOL21/Schumacher/schu5.tex
