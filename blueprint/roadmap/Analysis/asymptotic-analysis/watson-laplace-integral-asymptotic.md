# Watson's lemma for Laplace integrals

Let $g : \mathbb{R} \to \mathbb{R}$ and let
$(c_k)_{k \ge 1}$ be real numbers such that for every $N \ge 0$,
$g(s) - \sum_{k=1}^{N} c_k s^k = O(s^{N+1})$ as $s \to 0^+$. Suppose there is $m_0 \in \mathbb{R}$
such that $s \mapsto g(s) e^{-ms}$ is integrable on $(0, \infty)$ for every $m \ge m_0$. Then
for every $N \ge 0$,
$\int_0^\infty g(s) e^{-ms} \, ds - \sum_{k=1}^{N} k! \, c_k / m^{k+1} = O(1 / m^{N+2})$ as
$m \to \infty$.

The case $N = 0$ of the hypothesis says $g(s) = O(s)$ as $s \to 0^+$: the expansion of $g$ has no
constant term.

## Sources

- <https://cs.uwaterloo.ca/journals/JIS/VOL14/Nemes/nemes4.tex>, lines 142-151.
