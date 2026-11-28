# Asymptotic enumeration of planar, tree-child and galled level-2 networks

**Networks.** A (binary) phylogenetic network with $n$ leaves is a rooted acyclic digraph whose sinks are labelled bijectively by $\{1,\ldots,n\}$, in which the root has one child (if $n>1$), each leaf has one parent, each interior node is a tree node (one parent, two children) or a reticulation (two parents, one child), and each 2-connected component with at least three vertices has at least two outgoing cut arcs. It is *level-2* if every 2-connected component contains at most two reticulations; *tree-child* if every interior node has a child that is a tree node or a leaf; *galled* if every reticulation lies in a unique tree cycle; *GTC* if galled and tree-child. Planarity classes satisfy planar $\supset$ upward planar $\supset$ terminal planar (root and leaves on the outer face) $\supset$ outer planar.

**Planarity facts.** All level-1 networks are outer planar. All level-2 networks are upward planar, and a level-2 network is terminal planar if and only if it is outer planar. So for level-2 networks only two planarity regimes remain: unrestricted and terminal (= outer) planar.

**Functional equation (tree-child case).** The exponential generating function $T(x)=\sum_{n\ge1}t_n x^n/n!$ of level-2 tree-child networks satisfies, writing $U=\frac{1}{1-T}$,

$$T = x + \frac{T^2}{2} + \frac12\big(U^2-1\big)T + \frac32\,U^2\,\frac{T}{1-T}\big(U^2-1\big)T + U^4\big(U^2-1\big)T^2 + \frac14\,U^2\big(U^2-1\big)^2T^2.$$

Comparing coefficients gives $t_1,t_2,\ldots = 1, 3, 66, 2235, 99990, 5732775, \ldots$ (the source's list prints $t_5 = 99900$; iterating the equation gives $99990$)

**Theorem.** The numbers $t_n$ of level-2 tree-child networks with $n$ leaves satisfy

$$t_n \sim c\, n^{n-1}\gamma^n, \qquad c\approx 0.0667418464,\quad \gamma\approx 4.6710490708,$$

and each of the seven subclasses in the table (together with the general class) has the same form $N_n\sim c\,n^{n-1}\gamma^n$ with the constants

| level-2 class | general | tree-child | galled | GTC |
|---|---|---|---|---|
| arbitrary / planar / upward planar | $c=0.02931010$, $\gamma=15.4332995$ | $c=0.06674185$, $\gamma=4.67104907$ | $c=0.05885954$, $\gamma=6.42241234$ | $c=0.07888067$, $\gamma=3.98275804$ |
| terminal planar / outer planar | $c=0.03486095$, $\gamma=12.9230111$ | $c=0.07450612$, $\gamma=4.33252428$ | $c=0.06965278$, $\gamma=5.39994365$ | $c=0.08586449$, $\gamma=3.83201916$ |

The general level-2 rate $15.43$ (and the level-1 rate $2.94$) were known earlier; terminal planarity lowers the general rate to $12.92$ but changes the tree-child and galled rates only slightly, and the terminal planar GTC rate $3.83$ is close to the level-1 rate.

## Expansion

Each class is decomposed at the root: a network is a leaf, a tree node joining two smaller networks, or one of finitely many level-2 generator types (blobs) whose sides carry sequences of smaller networks; the factors $U=1/(1-T)$ count such sequences, and planarity or the tree-child and galled conditions restrict which generators and attachments are allowed. Rewriting the resulting implicit equation in the form $T=x\,\phi(T)$, the singular inversion theorem applies: if $C=z\phi(C)$ with $\phi$ analytic, aperiodic, nonlinear with nonnegative coefficients, $\phi(0)\neq0$, and $\tau$ the unique positive root of $\phi(\tau)=\tau\phi'(\tau)$ inside the disc of convergence, then $C$ has radius $\rho=\tau/\phi(\tau)$, a square-root singularity there, and $[z^n]C\sim\sqrt{\phi(\tau)/(2\phi''(\tau))}\,\rho^{-n}/\sqrt{\pi n^3}$. Multiplying by $n!$ and using Stirling's formula turns $\rho^{-n}n^{-3/2}n!$ into the form $c\,n^{n-1}\gamma^n$ with $\gamma=1/(e\rho)$.

## Sources

- Hexuan Liu, Bing-Ze Lu, Taoyang Wu, Guan-Ru Yu, "Asymptotic enumeration of subclasses of level-2 phylogenetic networks", in Proceedings of the 13th European Conference on Combinatorics, Graph Theory and Applications (EUROCOMB 2025) (no DOI found for this extended abstract). Published version of arXiv:2601.21578, cited next; locators there refer to the arXiv version.
- Hexuan Liu, Bing-Ze Lu, Taoyang Wu and Guan-Ru Yu, "Asymptotic Enumeration of Subclasses of Level-2 Phylogenetic Networks", arXiv:2601.21578 (2026), Section 1 (definitions, Proposition 1.1), Section 2 (Theorem 2.1 and its table, Remark 2.2), Section 3 (Lemma 3.1, Theorem 3.2), <https://doi.org/10.48550/arXiv.2601.21578>.
