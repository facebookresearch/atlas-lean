# The meta-automatic sequence $\mathcal{M}_2$

The meta-automatic sequence
$\mathcal{M}_2 : \mathbb{N} \to \{0, 1\}$ (OEIS A391614) is defined by $\mathcal{M}_2(0) = 0$,
$\mathcal{M}_2(1) = 1$, $\mathcal{M}_2(4n) = \mathcal{M}_2(2n + \mathcal{M}_2(n))$ and
$\mathcal{M}_2(4n+1) = 1 - \mathcal{M}_2(4n)$ for $n \ge 1$, and
$\mathcal{M}_2(4n+2) = \mathcal{M}_2(2n + 1 - \mathcal{M}_2(n))$ and
$\mathcal{M}_2(4n+3) = 1 - \mathcal{M}_2(4n+2)$ for $n \ge 0$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Section 4 (definition of `ℳ₂`).
