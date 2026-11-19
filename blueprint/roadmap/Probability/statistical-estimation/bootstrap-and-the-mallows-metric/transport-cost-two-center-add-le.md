# Centring decreases the Mallows metric by the squared distance of the means

Let $\mu, \nu$ be probability measures with finite second moments on a separable real Hilbert space, with means $a = \int x \, d\mu$ and $b = \int x \, d\nu$. For $U \sim \mu$ and $V \sim \nu$,

$$d_2(U - EU, V - EV)^2 + \|a - b\|^2 \le d_2(U, V)^2 ,$$

where the left-hand distance is between the laws of $U - a$ and $V - b$.

Bickel and Freedman prove the equality $d_2(U, V)^2 = d_2(U - EU, V - EV)^2 + \|EU - EV\|^2$. This page is the inequality above, the half of the lemma used to centre the summands in Mallows' contraction; the equality is [Mallows metric and centring](transport-cost-two-eq-center-add.md). For every coupling $\pi$ of $\mu$ and $\nu$, its image under $(x, y) \mapsto (x - a, y - b)$ couples the centred laws, and expanding the square gives $\int \|(x - y) - (a - b)\|^2 \, d\pi = \int \|x - y\|^2 \, d\pi - \|a - b\|^2$.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.8 (the first inequality of its proof).
