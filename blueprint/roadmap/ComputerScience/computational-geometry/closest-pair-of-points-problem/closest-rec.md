# Closest-pair recursion

Let $K$ be a linearly ordered field and $c_1, \dots, c_n$ a list
of points $c_i = (x_i, y_i)$ of $K^2$. If $n \le 3$, the recursion returns the brute-force scan of
the list. Otherwise let $m = \lfloor n/2 \rfloor$, and run the recursion on $c_1, \dots, c_m$ and
on $c_{m+1}, \dots, c_n$. If neither call returns a value, it returns no value. Otherwise let
$\delta$ be the least of the returned values, let $T$ be the list of the points $c_i$ with
$(x_i - x_m)^2 < \delta$ in their original order, sorted by second coordinate with a stable merge
sort, and run the strip scan with threshold $\delta$ on $T$. The recursion returns
$\min(\delta, s)$ if the strip scan returns a value $s$, and $\delta$ otherwise. In the base case
its cost is that of the brute-force scan; otherwise it is the sum of the costs of the two
recursive calls and of the strip scan when it is run, and splitting, filtering and sorting are
free.
