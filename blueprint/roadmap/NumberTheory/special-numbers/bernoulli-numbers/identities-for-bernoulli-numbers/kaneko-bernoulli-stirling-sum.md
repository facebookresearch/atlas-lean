# Kaneko's Stirling-number formula for the Bernoulli numbers

Let $B_n$ denote the $n$-th
Bernoulli number, with $B_1 = -1/2$, and let $S(n, j)$ denote the Stirling numbers of the second
kind. For every natural number $n$,

$$B_n = \sum_{m=1}^{n+1} \frac{(-1)^{m-1} (m-1)!\, S(n, m-1)}{m}.$$

This is Kaneko's explicit formula for the poly-Bernoulli numbers $B_n^{(k)}$ at $k = 1$. That
formula carries a factor $(-1)^n$, which cancels against $B_n^{(1)} = (-1)^n B_n$ (the numbers
$B_n^{(1)}$ come from the generating series $t/(1 - e^{-t})$).

## Sources

- Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers," Journal of Integer Sequences 10 (2007), Article 07.4.1, Theorem [Kaneko1] (label 1), lines 144–152, https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex citing M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des Nombres de Bordeaux 9 (1997), 221–228.
