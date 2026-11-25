# Selection path measure by exponential change of measure

Let $\alpha \in \mathbb R$, let $P^0_x$ be the law on $C([0, \infty), [0, 1])$ of the continuous neutral Wright–Fisher process without mutation started at $x \in [0, 1]$, with canonical filtration $(\mathcal F_t)$, and let $Z^\alpha$ be the [selection density on neutral path space](selection-density-on-neutral-path-space-no-stoch.md). The measures $Z^\alpha_t \cdot P^0_x$ on $\mathcal F_t$, $t \ge 0$, are consistent: the restriction of $Z^\alpha_t \cdot P^0_x$ to $\mathcal F_s$ is $Z^\alpha_s \cdot P^0_x$ for $s \le t$. They therefore extend to a unique probability measure $P^\alpha_x$ on the canonical $\sigma$-field with $P^\alpha_x|_{\mathcal F_t} = Z^\alpha_t \cdot P^0_x$ for every $t$, and $x \mapsto P^\alpha_x(A)$ is measurable for every measurable set $A$. For $\alpha = 0$, $P^\alpha_x = P^0_x$.

## Depends on

- [Selection density on neutral path space without stochastic integrals](selection-density-on-neutral-path-space-no-stoch.md)

## Proof depends on

- [Law of a continuous modification on the space of continuous paths, measurable in the initial point](law-of-a-continuous-modification-on-c-0-infinity.md)
- [Canonical path measure of the raw Wright–Fisher process](raw-measure.md)

## Expansion

A full proof page must still establish:

- consistency from the martingale property of $Z^\alpha$;
- the extension of the consistent family to the canonical $\sigma$-field of $C([0, \infty), [0, 1])$, and measurability in $x$;
- the case $\alpha = 0$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, Section 3, and Chapter 10, <https://doi.org/10.1002/9780470316658>
- A. Etheridge, *Some Mathematical Models from Population Genetics*, École d'Été de Probabilités de Saint-Flour XXXIX-2009, Lecture Notes in Mathematics 2012, Springer, 2011, <https://link.springer.com/book/10.1007/978-3-642-16632-7> (background)
