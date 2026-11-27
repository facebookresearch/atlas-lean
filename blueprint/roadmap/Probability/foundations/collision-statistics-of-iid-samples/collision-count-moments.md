# Mean and variance of collision and cross-collision counts

For a tuple $x \in \alpha^k$ let $C(x) = \#\{i < j : x_i = x_j\}$ be its *collision count*, and for $x \in \alpha^k$, $y \in \alpha^l$ let $D(x,y) = \#\{(i,j) : x_i = y_j\}$ be the *cross-collision count*. Let $x$ be $k$ i.i.d. draws from $p$ and, independently, $y$ be $l$ i.i.d. draws from $q$, on a finite set $\alpha$. Write $s = \sum_a p(a)^2$, $t_3 = \sum_a p(a)^3$, $t = \sum_a p(a)q(a)$, $u = \sum_a p(a)q(a)^2$, $v = \sum_a p(a)^2 q(a)$. Then

1. $\mathbb{E}[C(x)] = \binom{k}{2} s$ and $\mathrm{Var}[C(x)] = \binom{k}{2}(s - s^2) + k(k-1)(k-2)(t_3 - s^2)$;
2. $\mathbb{E}[D(x,y)] = klt$ and $\mathbb{E}[D(x,y)^2] = klt + k(k-1)l\,v + kl(l-1)\,u + k(k-1)l(l-1)\,t^2$;
3. $\mathbb{E}[C(x) D(x,y)] = \tfrac12 k(k-1)(k-2)\,l\,s\,t + k(k-1)l\,v$.

These are the moments behind collision-based uniformity and closeness testers.

## Proof sketch

Write both counts through occurrence counts $N_a(x) = \#\{i : x_i = a\}$: $C = \sum_a \binom{N_a}{2}$ and $D = \sum_a N_a(x)N_a(y)$. The joint moments of occurrence counts of i.i.d. samples follow by peeling off one draw at a time; independence of $x$ and $y$ factorizes the cross terms. Collecting terms by the pattern of coinciding indices gives the formulas.

## Sources

- Ilias Diakonikolas, Themis Gouleakis, John Peebles and Eric Price, "Collision-Based Testers are Optimal for Uniformity and Closeness", Chicago Journal of Theoretical Computer Science, 2019.
- Oded Goldreich and Dana Ron, "On Testing Expansion in Bounded-Degree Graphs", Electronic Colloquium on Computational Complexity, 2000.
