# The meta-automatic sequence $\mathcal{M}_1$

The sequence
$\mathcal{M}_1 : \mathbb{N} \to \{0, 1\}$ (OEIS A392736) is defined by $\mathcal{M}_1(0) = 0$,
$\mathcal{M}_1(1) = 1$, the recurrences $\mathcal{M}_1(4n) = \mathcal{M}_1(n)$ and
$\mathcal{M}_1(4n+1) = 1 - \mathcal{M}_1(n)$ for every $n \ge 1$, and the recurrences
$\mathcal{M}_1(4n+2) = \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$ and
$\mathcal{M}_1(4n+3) = 1 - \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$ for every $n \ge 0$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Section 3 (definition of `ℳ₁`).
