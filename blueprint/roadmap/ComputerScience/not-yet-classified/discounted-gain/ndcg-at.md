# Normalized discounted cumulative gain

For a cutoff $k \le N$, gains $g$ on $N$ candidates, nonnegative nonincreasing discounts $w_1, \dots, w_k$, a ranked prefix $r_1, \dots, r_k$ and a permutation $s$ of the candidates sorting the gains in nonincreasing order, the normalized discounted cumulative gain at $k$ is

$$\frac{\sum_{i \le k} w_i\, g(r_i)}{\sum_{i \le k} w_i\, g(s_i)},$$

with value $0$ when the denominator, the ideal DCG, is $0$.
