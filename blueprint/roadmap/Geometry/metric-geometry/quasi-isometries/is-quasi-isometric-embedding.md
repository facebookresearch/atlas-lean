# Quasi-isometric embedding

A map $f : X \to Y$ between pseudometric spaces is an $(L, C)$-quasi-isometric embedding if $L \ge 1$, $C \ge 0$ and

$$\frac{d(x, y)}{L} - C \le d(f x, f y) \le L\, d(x, y) + C \quad \text{for all } x, y \in X.$$

Such a map controls distances up to a multiplicative factor at large scale and ignores everything below scale $C$: it need not be continuous or injective. These are the distance inequalities of a quasi-isometry in its now-standard $(L, C)$ form, which matches Gromov's 1993 formulation (§0.2.C: quasi-isometries are the compositions of Hausdorff and Lipschitz equivalences). Gromov's earlier formulation (Proc. ICM 1983, §1.B) uses "virtually Lipschitz" maps; it agrees with the $(L, C)$ form when both spaces are uniformly discrete, for instance for word metrics, but not in general: the floor map $\mathbb{R} \to \mathbb{Z}$ is a $(1, 1)$-quasi-isometry, while every Lipschitz map $\mathbb{R} \to \mathbb{Z}$ is constant. Gromov defines quasi-isometries, not quasi-isometric embeddings; the embedding is the distance half of the definition.

## Sources

- M. Gromov, *Asymptotic invariants of infinite groups*, in *Geometric Group Theory*, vol. 2 (G. A. Niblo and M. A. Roller, eds.), London Math. Soc. Lecture Note Ser. 182, Cambridge University Press, 1993, §0.2.C.
