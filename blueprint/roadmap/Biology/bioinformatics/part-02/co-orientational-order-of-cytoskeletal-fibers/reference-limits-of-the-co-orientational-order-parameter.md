# Reference limits of the co-orientational order parameter

**Setting.** Let $P = \{\vec p_i\}$ and $Q = \{\vec q_i\}$ be two families of planar unit pseudo-vectors at the same sites, with orientational order parameters $\mathrm{OOP}_P$, $\mathrm{OOP}_Q$ and co-orientational order parameter $\mathrm{COOP}_{PQ}$, as in [Orientational and co-orientational order parameters](orientational-and-co-orientational-order-parameters.md). By rotation invariance take both directors along $(1, 0)$, so $\mathrm{OOP}_K = \langle \cos 2\varphi^K_i\rangle$ and $\langle \sin 2\varphi^K_i\rangle = 0$.

**Uncorrelated limit.** If the orientations of $P$ and $Q$ are independent, then

$$\mathrm{COOP}_u = \big\langle 2(p_{i,x} q_{i,x} + p_{i,y} q_{i,y})^2 - 1 \big\rangle = \langle 2p_{i,x}^2 - 1\rangle\,\langle 2 q_{i,x}^2 - 1\rangle = \mathrm{OOP}_P \cdot \mathrm{OOP}_Q .$$

**Noisy-correlated limit.** If $Q$ is $P$ with each fiber rotated by an independent random noise angle (so $Q$ is the less ordered family), then

$$\mathrm{COOP}_c = \frac{\min(\mathrm{OOP}_P, \mathrm{OOP}_Q)}{\max(\mathrm{OOP}_P, \mathrm{OOP}_Q)} .$$

**These are reference values, not extrema.** An explicit two-fiber construction ("anti-correlated" families correlated in two different ways) gives $\mathrm{COOP} < \mathrm{COOP}_u$, and pairing angles in decreasing order ("ultra-correlated" families) gives $\mathrm{COOP} > \mathrm{COOP}_c$. For two families with random biological variability, $\mathrm{COOP}_u$ and $\mathrm{COOP}_c$ bracket the observed value and calibrate how strongly the families' orientations are coupled.

## Depends on

- [Orientational and co-orientational order parameters](orientational-and-co-orientational-order-parameters.md)

## Expansion

*Uncorrelated.* With $\varphi^P_i, \varphi^Q_i$ the fiber angles, $2(\vec p_i \cdot \vec q_i)^2 - 1 = \cos 2(\varphi^P_i - \varphi^Q_i) = \cos 2\varphi^P_i \cos 2\varphi^Q_i + \sin 2\varphi^P_i \sin 2\varphi^Q_i$. Under independence the expectation factors, the sine terms vanish because both directors lie along $(1,0)$, and what remains is $\mathrm{OOP}_P\, \mathrm{OOP}_Q$. The same factorization kills the off-diagonal entry $\langle \sin 2\theta_i\rangle$ of $\mathbb T_{PQ}$, so this diagonal entry is its largest eigenvalue.

*Noisy-correlated.* Write $\varphi^Q_i = \varphi^P_i - \theta_i$ with $\theta_i$ independent of $\varphi^P_i$ and directors aligned, so $\langle \sin 2\theta_i\rangle = 0$, $\mathrm{COOP} = \langle\cos 2\theta_i\rangle$, $\mathrm{OOP}_P = \langle \cos 2\varphi^P_i\rangle$. Then $\langle \cos 2(\varphi^P_i - \theta_i)\rangle = \langle\cos 2\varphi^P_i\rangle\langle \cos 2\theta_i\rangle + \langle \sin 2\varphi^P_i\rangle \langle \sin 2\theta_i \rangle$, so $\mathrm{OOP}_Q = \mathrm{OOP}_P \cdot \mathrm{COOP}_c$; solving and using $\mathrm{OOP}_Q \le \mathrm{OOP}_P$ gives the ratio.

## Sources

- N. K. Drew, M. A. Eagleson, D. B. Baldo, K. K. Parker, A. Grosberg, "Metrics for assessing cytoskeletal orientational correlations and consistency", *PLoS Computational Biology* 11(4) (2015) e1004190. Theorem 4 (uncorrelated COOP, Eqs. (20)–(22)), Theorem 5 (anti-correlated COOP), Theorem 6 (correlated COOP, Eqs. (28)–(30)), Theorem 7 (ultra-correlated COOP). <https://doi.org/10.1371/journal.pcbi.1004190>. PMCID: PMC4388480.
