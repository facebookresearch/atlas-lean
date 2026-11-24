# Hoeffding extremal lunar numbers

Let $b$ and $n$ be natural numbers and $d$ a real
number. Let $\mathcal{L}_b^n$ be the set of lunar numbers of base $b$ and degree at most $n$
(digit strings $c_0, \dots, c_n$ with digits in $\{0, \dots, b - 1\}$), with the max-min product
$\otimes$, and for $f \in \mathcal{L}_b^n$ let $|f_i|$ be the number of its digits that are at
least $i$. The set $\mathcal{H}_b^n(d)$ of $d$-Hoeffding extremal lunar numbers consists of the
$h \in \mathcal{L}_b^n$ for which there is an index $i$ with $1 \le i \le b - 1$ such that either
$\bigl||h_i| - (b - i)n/b\bigr| > d/2$, or $h = f \otimes g$ for some $f, g \in \mathcal{L}_b^n$
with $\bigl||f_i| + |g_i| - (b - i)(n + 1)/b\bigr| > d/2$.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Definition 23.
