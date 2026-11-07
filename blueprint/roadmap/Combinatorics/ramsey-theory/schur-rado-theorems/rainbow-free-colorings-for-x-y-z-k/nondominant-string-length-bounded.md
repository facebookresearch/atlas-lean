# Non-dominant monochromatic strings have bounded length

Let $k$ be a natural number, let
$n_0 \ge 2$ be an integer, and let $c$ be a coloring of the positive integers by three colors
with no rainbow solution of $x - y = z^k$: there are no positive integers $x, y, z$ with
$x = y + z^k$ and $c(x)$, $c(y)$, $c(z)$ pairwise distinct. For a color $e$ write $N_e(n)$ for
the number of $x \in \{1, \dots, n\}$ with $c(x) = e$, and assume that for every real $M$ there
are arbitrarily large $n$ with $N_e(n) - n / n_0 > M$ for all three colors $e$, that is,
$\limsup_{n \to \infty} \bigl(\min_e N_e(n) - n / n_0\bigr) = \infty$. Let $d$ be a dominant
color: for all positive integers $i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on
$\{i, i + 1, \dots, i + \ell - 1\}$, then one of them is $d$. Then there is an $L$ such that for
all positive integers $i$ and all $\ell \ge 0$, if $c(i) \ne d$ and $c(i + t) = c(i)$ for all
$0 \le t < \ell$, then $\ell \le L$.

## Sources

- Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 4.
