# Forced blue points on a diagonal give a monochromatic L

Let $n \ge 3$, write
$[n] = \{1, \dots, n\}$, let $c$ be a coloring of $\mathbb{N} \times \mathbb{N}$ with $3$ colors
and let red and blue be two distinct colors. Let $s \ge 1$ and let $X$ be a finite set of
natural numbers such that every $x \in X$ satisfies $x \ge 1$ and $x + s \le n$, the point
$(x + s, x)$ is blue, and the points $(x, x)$ and $(x + s, x + s)$ are red (so red at
$(x + s, x)$ would complete the red L $(x, x)$, $(x + s, x)$, $(x + s, x + s)$). If
$\binom{|X|}{2} > n - 2$, then $c$ has a monochromatic L in $[n] \times [n]$: positive integers
$x$, $y$, $d$ with $x + d \le n$ and $y + d \le n$ such that the points $(x, y)$, $(x + d, y)$
and $(x + d, y + d)$ all have the same color.

The paper states the threshold as $|X| \ge \lceil \sqrt{2n - 15/4} + 1/2 \rceil$, meant as the
least $b$ with $\binom{b}{2} > n - 2$. This closed form is one too small when
$\sqrt{2n - 15/4} + 1/2$ is an integer, and the lemma then fails: for $n = 3$, color the
diagonal red, $(2, 1)$, $(3, 2)$, $(2, 3)$ blue, $(3, 1)$ green and $(1, 2)$, $(1, 3)$ red; with
$s = 1$ there are two forced blue points and no monochromatic L.

## Sources

- Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Lemma 1.
