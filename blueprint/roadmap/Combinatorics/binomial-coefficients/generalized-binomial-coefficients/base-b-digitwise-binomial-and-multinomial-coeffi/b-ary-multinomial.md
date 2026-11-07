# The $b$-ary multinomial coefficient

Let $b \ge 2$, let $n$ be a natural number and let
$(k_1, \dots, k_m)$ be a list of natural numbers, and write $n_l$ and $(k_i)_l$ for the rank-$l$
base-$b$ digits of $n$ and $k_i$ (taken to be $0$ beyond the last digit, with $0$ having no
digits). Let $N$ be the largest of the numbers of base-$b$ digits of $n, k_1, \dots, k_m$. The
$b$-ary multinomial coefficient of $n$ over $(k_1, \dots, k_m)$ is $\prod_{l=0}^{N-1} c_l$, where
$c_l = \frac{n_l!}{(k_1)_l! \cdots (k_m)_l!}$ if $(k_1)_l + \dots + (k_m)_l = n_l$ and $c_l = 0$
otherwise.

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex, lines 349-359.
