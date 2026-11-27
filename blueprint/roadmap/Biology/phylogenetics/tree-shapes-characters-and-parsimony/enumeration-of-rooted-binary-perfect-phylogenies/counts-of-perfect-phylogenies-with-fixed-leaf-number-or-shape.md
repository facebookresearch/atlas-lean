# Counts of rooted binary perfect phylogenies with fixed leaf number or tree shape

**Setting.** A rooted binary perfect phylogeny with sample size $s$ and $n$ leaves is a rooted binary unlabeled tree with $n$ leaves whose leaves carry positive integers summing to $s \ge n$, up to swapping sibling subtrees. Let $b_{s,n}$ count them, $N_{s,T}$ count those with a given unlabeled shape $T$, and $g_{s,n} = N_{s,T}$ for the caterpillar shape $T$ with $n$ leaves.

**Proposition (fixed number of leaves).** $b_{s,1} = 1$, and for $s \ge n \ge 2$

$$b_{s,n} = \sum_{j=1}^{n-1}\sum_{i=j}^{s-n+j} \tfrac12\, b_{s-i,n-j}\, b_{i,j} + \tfrac12\, b_{s/2,n/2}\,\mathbf{1}\{s,n \text{ both even}\}.$$

The generating functions $B_n(z) = \sum_s b_{s,n} z^s$ satisfy $B_1(z) = z/(1-z)$ and $B_n(z) = \sum_{j=1}^{n-1}\tfrac12 B_{n-j}(z)B_j(z) + \tfrac12 B_{n/2}(z^2)$ (last term only for even $n$). In closed form,

$$b_{s,2} = \left\lfloor \frac s2 \right\rfloor, \qquad b_{s,3} = \left\lfloor \frac{s-1}{2} \right\rfloor\left\lceil \frac{s-1}{2} \right\rceil, \qquad b_{s,4} = \begin{cases} \dfrac{(s-1)(s-3)(5s-1)}{48}, & s \ge 5 \text{ odd},\\[1ex] \dfrac{s(s-2)(5s-11)}{48} + \dfrac12\left\lfloor \dfrac s4 \right\rfloor, & s \ge 4 \text{ even}. \end{cases}$$

**Proposition (fixed shape).** If $T$ has one leaf, $N_{s,T} = 1$. If $T$ has root subtrees $T_\ell, T_r$ and $s \ge |T| \ge 2$,

$$N_{s,T} = \begin{cases} \displaystyle\sum_{i=|T_\ell|}^{s-|T_r|} N_{i,T_\ell}\,N_{s-i,T_r}, & T_\ell \neq T_r,\\[1ex] \displaystyle\sum_{i=|T_\ell|}^{s-|T_r|} \tfrac12 N_{i,T_\ell}\,N_{s-i,T_r} + \tfrac12 N_{s/2,T_\ell}, & T_\ell = T_r. \end{cases}$$

For caterpillars, $g_{s,2} = \lfloor s/2 \rfloor$, $g_{s,n} = \sum_{i=n-1}^{s-1} g_{i,n-1}$ for $s \ge n \ge 3$, and

$$G_n(z) = \sum_{s \ge n} g_{s,n} z^s = \frac{z^n}{(1-z)^n(1+z)}.$$

## Expansion

All recursions come from decomposing at the root and halving to correct for the unordered pair of root subtrees, with the diagonal term restoring the symmetric configurations counted once. For $n = 2$ the two leaf values form an unordered pair of positive integers summing to $s$, giving $\lfloor s/2 \rfloor$. In a caterpillar the deepest cherry is the only symmetric node, contributing the factor $z^2/((1-z)(1-z^2))$, and each further leaf hung off the spine contributes an independent factor $z/(1-z)$, which yields $G_n$.

## Sources

- Chloe E. Shiff and Noah A. Rosenberg, "Enumeration of rooted binary perfect phylogenies", Discrete Applied Mathematics 380 (2026), 538–561, <https://doi.org/10.1016/j.dam.2025.10.053>; numbering as in arXiv:2410.14915: Proposition 6, Corollaries 7–9, Proposition 10 (Section 4), Propositions 11, 14 and 15 (Section 5).
