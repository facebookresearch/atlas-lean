# Stirling-type asymptotic expansions of the Catalan numbers

Let $C_n$ be the $n$-th Catalan
number and $B_k$ the $k$-th Bernoulli number, and let $(E_k)$ be a sequence of integers with
$E_0 = 1$ and $\sum_{j=0}^{\lfloor n/2 \rfloor} \binom{n}{2j} E_{n-2j} = 0$ for every $n > 0$
(these are the Euler numbers $1, 0, -1, 0, 5, \dots$). For $k \ge 1$ put
$c_k = (-1)^{k+1} \left((2^{-k} - 2) B_{k+1} - k - 1\right) / (k (k + 1))$ and
$d_k = 2^{-4k-2} (4 - E_{2k}) / k$. Then for every $m \ge 0$, as $n \to \infty$,
$\log\left(C_n \, n \sqrt{\pi n} / 4^n\right) = \sum_{k=1}^{m} c_k n^{-k} + o(n^{-m})$ and,
writing $x = n + 3/4$,
$\log\left(C_n \sqrt{\pi x^3} / 4^n\right) = \sum_{k=1}^{m} d_k x^{-2k} + o(x^{-2m})$.

The first coefficient is $c_1 = -9/8$, matching the classical expansion
$C_n = \frac{4^n}{\sqrt{\pi} \, n^{3/2}} \left(1 - \frac{9}{8n} + \dots\right)$.

Proof: The Catalan recurrence gives a logarithmic first-difference equation.
Telescoping its Bernoulli-polynomial expansion yields both all-orders formulas.

## Sources

- Neven Elezović, "Asymptotic Expansions of Central Binomial Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014), Article 14.2.1, Catalan Stirling-type theorem (unlabeled, equation 42), lines 626–637, https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex
