# $\mathcal{M}_1$ as a coding of a uniform morphism fixed point

Let $\sigma$ be the
$4$-uniform morphism on $\{0, 1, 2, 3\}$ with $\sigma(0) = 0112$, $\sigma(1) = 1230$,
$\sigma(2) = 2301$ and $\sigma(3) = 3023$, and write $\sigma(c)_r$ for the letter of $\sigma(c)$
at position $r$, counted from $0$. There is a sequence $w : \mathbb{N} \to \mathbb{N}$ with
$w(0) = 0$ and $w(4n + r) = \sigma(w(n))_r$ for all $n \in \mathbb{N}$ and $r < 4$, such that,
reading the values of the meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$,
$\mathcal{M}_1(n) = w(n) \bmod 2$ for every $n \in \mathbb{N}$. In other words, $\mathcal{M}_1$
is the image of the fixed point of $\sigma$ starting with $0$ under the coding $0, 2 \mapsto 0$,
$1, 3 \mapsto 1$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Corollary 16 (`jis-2026-26.4.1-cor-16`).
