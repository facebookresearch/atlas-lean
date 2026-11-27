# Distributed defective colouring in O(log* n) rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. For every integer $1 \le d \le \Delta$, a $d$-defective $O\bigl((\Delta/d)^2\bigr)$-colouring can be computed deterministically in $O(\log^* n)$ rounds; in every round each vertex sends only its current colour, so the algorithm also runs in CONGEST. More generally, from an $M$-colouring with defect at most $d_0 \le d < \Delta$, an $O\bigl((\Delta - d_0)^2/(d + 1 - d_0)^2\bigr)$-colouring with defect at most $d$ can be computed in $O(\log^* M)$ rounds. As a consequence, a proper $(\Delta + 1)$-colouring can be computed deterministically in $O(\Delta + \log^* n)$ rounds.

## Proof sketch

Generalize Linial's colour reduction with set systems built from low-degree polynomials: a vertex of colour $x$ searches for an evaluation point $\alpha$ at which its polynomial $\varphi_x$ agrees with those of at most $d$ neighbours and takes the new colour $(\alpha, \varphi_x(\alpha))$; such an $\alpha$ exists when the number of evaluation points exceeds $\kappa(\Delta - d_0)/(d - d_0 + 1)$, where $\kappa$ bounds the agreements of two distinct polynomials. Iterating $O(\log^* M)$ times with suitably increasing intermediate defects gives the stated number of colours. For the proper colouring, colour a subgraph of maximum degree $D$ recursively: a $\lfloor D/2 \rfloor$-defective colouring with $O(1)$ colours splits it into classes of maximum degree at most $\lfloor D/2 \rfloor$, which are coloured in parallel with $\lfloor D/2 \rfloor + 1$ colours each, and the combined $O(D)$-colouring is compressed to $D + 1$ colours by colour reduction in $O(D)$ rounds. The compression step is needed because the combined palettes alone already exceed $D + 1$ colours.

## Depends on

- [Defective colouring](defective-colouring.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [The CONGEST model of distributed computing](../deterministic-network-decomposition/the-congest-model.md)

## Proof depends on

- [Linial's colour reduction to O(Delta^2) colours in O(log* n) rounds](linial-colour-reduction.md)

## Sources

- F. Kuhn, "Weak Graph Colorings: Distributed Algorithms and Applications", SPAA 2009, Lemma 4.1, Theorem 4.9, Algorithm 3 and Theorem 5.4.
- L. Barenboim, M. Elkin, F. Kuhn, "Distributed (Delta+1)-Coloring in Linear (in Delta) Time", SIAM Journal on Computing 43(1) (2014); STOC 2009.
