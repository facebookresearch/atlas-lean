# Shifting monochromatic strings by $k$-th powers

Let $k$ be a natural number and let $c$
be a coloring of the positive integers by three distinct colors $R$, $B$, $G$ with no rainbow
solution of $x - y = z^k$: there are no positive integers $x, y, z$ with $x = y + z^k$ and
$c(x)$, $c(y)$, $c(z)$ pairwise distinct. Assume that $R$ is dominant: for all positive integers
$i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on $\{i, i + 1, \dots, i + \ell - 1\}$,
then one of them is $R$. Let $j$ be a positive integer with $c(j) = B$, and let $i \ge 1$ and
$\ell \ge 0$ be such that $c(i + t) = G$ for all $0 \le t < \ell$. Then there is a color
$e \in \{B, G\}$ with $c(i + j^k + t) = e$ for all $0 \le t < \ell$, and, if $j^k < i$, there
is a color $e' \in \{B, G\}$ with $c(i - j^k + t) = e'$ for all $0 \le t < \ell$.

## Sources

- Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 2.
