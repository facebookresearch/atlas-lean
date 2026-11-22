# Cut norm

The cut norm of a symmetric kernel $u : \operatorname{Sym}^2 V \to \mathbb R$ on a finite vertex set is

$$\|u\|_\square = \frac{1}{|V|^2} \max_{S, T \subseteq V} \Big| \sum_{x \in S} \sum_{y \in T} u(x, y) \Big|,$$

read as $0$ when $V$ is empty.

For two weighted graphs $w, w'$ on the same vertex set, $\|w - w'\|_\square$ is their cut (rectangle) distance $d_\square$: two independent random graphs $G(n, 1/2)$ are close in cut distance with high probability (the distance tends to $0$), although they differ in about half of their pairs.

## Background

- [Cut norm of a kernel](graphon-cut-norm.md): the same norm for graphons, with sums replaced by integrals over measurable $S, T \subseteq [0,1]$.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, §4.1 (rectangular distance $d_\square$ and the matrix cut norm $\|A\|_\square$).
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, §2.3, equation (2.4) (Frieze and Kannan's cut distance).
