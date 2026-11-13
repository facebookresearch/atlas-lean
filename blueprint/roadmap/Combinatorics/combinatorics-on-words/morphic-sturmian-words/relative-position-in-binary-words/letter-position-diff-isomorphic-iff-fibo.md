# The Fibonacci word and its reflection are the words isomorphic to their gap sequences

Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite binary word over the letters $a$ and $b$ in
which both letters occur infinitely often. For a letter $\alpha$ let $p_\alpha(n)$ be
the position (counting from $0$) of the $n$-th occurrence of $\alpha$ in $w$ and
$\Delta p_\alpha(n) = p_\alpha(n+1) - p_\alpha(n)$. Call $\Delta p_a$ and $\Delta p_b$ codings of
$w$ if there are maps $\sigma_a, \sigma_b$ from $\{a, b\}$ to the natural numbers with
$\Delta p_a(n) = \sigma_a(\ell_{n-1})$ and $\Delta p_b(n) = \sigma_b(\ell_{n-1})$ for all
$n \ge 1$, and injective codings if moreover $\sigma_a$ and $\sigma_b$ are injective. Let
$f = abaab\cdots$ be the infinite Fibonacci word written with $a$ for $0$ and $b$ for $1$, and
$\bar f$ the word $f$ with $a$ and $b$ exchanged. Then $\Delta p_a$ and $\Delta p_b$ are injective
codings of $w$ if and only if $w = f$ or $w = \bar f$.

The paper's word "aperiodic" is dropped, as in Theorem 46 and Corollary 48.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 49 (`jis-2025-25.1.5-cor-49`).
