# Howard's formula for the series $\sum_{k \ge 0} 2x^k/(k+2)!$

Let $n$ be a natural
number, let

$$h(x) = \sum_{k \ge 0} \frac{2}{(k+2)!}\, x^k \in \mathbb{Q}[[x]],$$

let $h^{-1}$ be its inverse in $\mathbb{Q}[[x]]$, and write $[x^n]\, f$ for the coefficient of
$x^n$ in a power series $f$. Let $G_n \in \mathbb{Q}[X]$ be a polynomial of degree at most $n$
such that $G_n(m) = n!\, [x^n]\, (h^{-1})^m$ for every natural number $m \le n$. Then

$$G_n(X) = \sum_{i=0}^{n} (-1)^i\, 2^i\, \frac{n!\, i!}{(n+2i)!} \cdot
\frac{X(X+1)\cdots(X+i-1)}{i!} \cdot \frac{(X+n)(X+n-1)\cdots(X+i+1)}{(n-i)!} \cdot
B_{n+2i,\,i}(0, 1, 1, \dots),$$

where empty products equal $1$ and $B_{n+2i,\,i}(0, 1, 1, \dots)$ is the partial Bell
polynomial evaluated at the sequence whose first term is $0$ and whose other terms are all $1$.

## Sources

- G. Nemes, Journal of Integer Sequences 13 (2010). Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL13/Nemes/nemes2.tex Generic span: lines 120-133; specialization span: lines 166-173. File SHA256: f3556d7fdb4d3f9366c3505d2cd20564f431d71a337e9f3a4fc7c24431df2daf Span SHA256 (generic): c3e6c35fd19388416b9e1105e7b027a70c3956f58c8d204c44e88a0936273a04 Span SHA256 (specialization): bcc9e205ea075840eda33c04ff69e3f762b50e16bdc4627ed06ac9351fd4348c Statement IDs: jis_f8773fd39faf6ec979df6672 and jis_rank35_proof_specialization_lines_166_173 Grounded concept ID: jis_grounded_097dd40d7498e5b441a12749 Exact-rational probe: passed 75 comparisons across r=1,2,3, n=0,...,4, natural z=0,...,n+2; finite evidence only.
