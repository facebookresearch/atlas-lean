# Mallows metric and centring

Let $\mu, \nu$ be probability measures with finite second moments on a separable real Hilbert space, with means $a = \int x \, d\mu$ and $b = \int x \, d\nu$. For $U \sim \mu$ and $V \sim \nu$,

$$d_2(U, V)^2 = d_2(U - EU, V - EV)^2 + \|EU - EV\|^2 .$$

So the squared Mallows distance splits into a location part and a shape part.

The inequality $\ge$ is [centring decreases the Mallows metric](transport-cost-two-center-add-le.md). For $\le$, every coupling $\pi$ of the centred laws gives, through $(x, y) \mapsto (x + a, y + b)$, a coupling of $\mu$ and $\nu$ whose cost is that of $\pi$ plus $\|a - b\|^2$, because the mean displacement under $\pi$ is $0$.

## Informally uses

- [Centring decreases the Mallows metric by the squared distance of the means](transport-cost-two-center-add-le.md): the first half of the proof.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.8.
