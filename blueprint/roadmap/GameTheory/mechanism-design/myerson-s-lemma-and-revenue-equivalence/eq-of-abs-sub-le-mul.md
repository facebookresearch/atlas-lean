# Two-sided comparison lemma

Let $a \le b$ and let $D, g : \mathbb{R} \to \mathbb{R}$ satisfy
$|D(t) - D(s)| \le (g(t) - g(s))(t - s)$ for all $s \le t$ in $[a, b]$. Then $D(b) = D(a)$: summing
over a partition of $[a, b]$ into $n$ equal pieces bounds $|D(b) - D(a)|$ by
$(g(b) - g(a))(b - a)/n$ for every $n \ge 1$. (The hypothesis forces $g$ to be nondecreasing on $[a, b]$.)

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, proof of Lemma 2, where the corresponding step is the Riemann integrability of the monotone function `Q`.
