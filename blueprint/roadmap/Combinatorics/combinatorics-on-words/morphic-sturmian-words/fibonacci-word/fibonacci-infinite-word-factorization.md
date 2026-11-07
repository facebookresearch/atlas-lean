# The infinite Fibonacci word as $0$ followed by the finite Fibonacci words

Let $f$ be an
infinite word over $\{0, 1\}$ and let $f_1, f_2, f_3, \ldots$ be finite words over $\{0, 1\}$ with
$f_1 = 1$, $f_2 = 0$ and $f_{n+3} = f_{n+2} f_{n+1}$ for every natural number $n$, such that for
every natural number $n$ the word $f_{n+2}$ consists of the first $|f_{n+2}|$ letters of $f$.
Then for every natural number $N$ the word $w_N = 0\,f_1 f_2 \cdots f_N$ (so $w_0 = 0$) consists of
the first $|w_N|$ letters of $f$, and for every natural number $k$ the first $k$ letters of $f$
form a prefix of $w_N$ for some $N$. In this sense $f = 0 \cdot f_1 \cdot f_2 \cdot f_3 \cdots$.

## Sources

- Gabriele Fici, "Factorizations of the Fibonacci Infinite Word", Journal of Integer Sequences 18 (2015), Article 15.9.3, Proposition lines 188-195 (equation `fibo`), <https://cs.uwaterloo.ca/journals/JIS/VOL18/Fici/fici5.tex>.
