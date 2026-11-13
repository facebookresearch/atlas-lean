# Alfred's determinant of consecutive Fibonacci powers

Let $F_n$ denote the Fibonacci numbers
extended to all integers $n$ by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$, so that
$F_{-n} = (-1)^{n+1} F_n$. For every natural number $r$ and all integers $s$ and $k$, the
$(r+1) \times (r+1)$ integer matrix whose entry in row $i$ and column $j$, for
$0 \le i, j \le r$, is $F_{s+ik}^{\,r-j} \, F_{s+(i+1)k}^{\,j}$ has determinant
$(-1)^{|e|} \, F_k^{\binom{r+1}{2}} \prod_{\ell=1}^{r} F_{k\ell}^{\,r+1-\ell}$, where
$e = (s+1)\binom{r+1}{2} + k\binom{r+1}{3}$.

This is a slight variation of a result of Brother U. Alfred, "Some determinants involving
powers of Fibonacci numbers," Fibonacci Quarterly 2 (1964), 81–92.

## Sources

- Aram Tangboonduangjit and Thotsaporn Thanatipanonda, "Determinants Containing Powers of Generalized Fibonacci Numbers," Journal of Integer Sequences 19 (2016), Article 16.7.1, Corollary, lines 406–418, https://cs.uwaterloo.ca/journals/JIS/VOL19/Tangboonduangjit/aram5.tex
