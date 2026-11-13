# Thue–Morse quarto sequence

The Thue–Morse quarto sequence
$\mathcal{Q} : \mathbb{N} \to \{0, 1\}$ (OEIS A298952, with $\mathcal{Q}(0) = 0$) is given by
$\mathcal{Q}(0) = 0$, $\mathcal{Q}(1) = 1$ and, for every $m \ge 2$, writing $m = 4n + r$ with
$n \ge 0$ and $0 \le r \le 3$: $\mathcal{Q}(m) = \mathcal{Q}(n)$ if $r = 0$,
$\mathcal{Q}(m) = 1 - \mathcal{Q}(n)$ if $r = 1$, $\mathcal{Q}(m) = \mathcal{Q}(2n)$ if $r = 2$,
and $\mathcal{Q}(m) = 1 - \mathcal{Q}(2n)$ if $r = 3$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Section 2.2 (definition of `𝒬`).
