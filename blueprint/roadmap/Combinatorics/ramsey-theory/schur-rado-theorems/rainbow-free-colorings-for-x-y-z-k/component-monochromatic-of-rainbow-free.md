# Components avoiding the color of zero are monochromatic

Let $n$ and $t$ be natural
numbers, let $f$ be a map from $\mathbb{Z}/n\mathbb{Z}$ to itself, and let $c$ be a coloring of
$\mathbb{Z}/n\mathbb{Z}$ with $t$ colors that uses every color and is rainbow-free for
$x - y = f(z)$: no $x, y, z \in \mathbb{Z}/n\mathbb{Z}$ with $x - y = f(z)$ have $c(x), c(y), c(z)$
pairwise distinct. For $v \in \mathbb{Z}/n\mathbb{Z}$, call the set of $a$ with
$f^m(a) = f^{m'}(v)$ for some natural numbers $m, m'$ the component of $v$, where $f^m$ is the
$m$-th iterate of $f$. If no element of the component of $v$ has the color $c(0)$, then all its
elements have the same color.

The source record prints the equation as $x - y = f(x)$; the paper's proof uses the solution
$(f(a), 0, a)$ of $x - y = f(z)$, and the reading $x - y = f(x)$ fails on small examples.

## Sources

- Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 11 (`integers-2024-A105-lem-11`).
