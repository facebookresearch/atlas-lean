# No deterministic voting rule has metric distortion below three

For every deterministic voting rule $f$ and every $\varepsilon > 0$ there is an election with two candidates, a ranking profile and a consistent metric for which $\mathrm{SC}(f(\sigma), d) \ge (3 - \varepsilon) \min_c \mathrm{SC}(c, d)$. Hence $\mathrm{dist}(f) \ge 3$ for every deterministic rule.

## Proof sketch

Take candidates $a, b$ and an even number of voters split equally between $a \succ b$ and $b \succ a$. Whichever candidate $f$ picks, say $a$, place the voters preferring $a$ halfway between $a$ and $b$ (at distance $1$ from both, with ties broken consistently) and the voters preferring $b$ at $b$, with $d(a,b) = 2$: then $\mathrm{SC}(a) = n/2 \cdot 1 + n/2 \cdot 2$ and $\mathrm{SC}(b) = n/2 \cdot 1$, a ratio of $3$ in the limit of small perturbations.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Sources

- E. Anshelevich, O. Bhardwaj, E. Elkind, J. Postl, P. Skowron, "Approximating optimal social choice under metric preferences", Artificial Intelligence 264 (2018); AAAI 2015.
