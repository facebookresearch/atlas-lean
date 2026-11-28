# Flat foldings of crease patterns

A crease pattern is a region of the plane with a system of line-segment creases. A flat folding maps it to the plane isometrically away from the creases, reflecting across each crease, together with a stacking order of the layers that some nearby non-self-intersecting embedding in space realizes.

**Definitions (Eppstein).** A *crease pattern* $P$ is a subset of the plane together with a system of creases (line segments, possibly infinitely many). A *local flat folding* of $P$ is a continuous map $\varphi$ from $P$ to the plane that is an isometry on every open subset meeting no crease, and that identifies the two points of each pair of mirror images across $c$ in every open subset containing a single crease $c$. The images of the creases partition the plane into *cells*; the *ply* of a cell is the number of its preimages. A *layering* chooses, for each cell, a vertical order of its preimages. A *flat folding* is a local flat folding with a layering such that, for every $\varepsilon > 0$, the layering is consistent with a topological embedding of $P$ in three-dimensional space that is $\varepsilon$-close to the local flat folding. In a *labeled* crease pattern each crease is marked as a mountain or valley fold, and the layering must respect the labels; in an *unlabeled* one either fold direction is allowed. $P$ is *flat-foldable* if it has a flat folding.

For finite crease patterns, a local flat folding is determined up to rigid motion when it exists and can be found in linear time, and a local flat folding comes from a flat folding exactly when it has a layering that is *uncrossed*: at each crease, uncreased layers do not cross, no uncreased layer passes between two layers joined by a crease (taco-tortilla), creased pairs on the same crease line do not alternate (taco-taco), and fold labels are respected.

A point is *crumpled* if every neighborhood of it meets infinitely many creases. A crease pattern is *tame* if it is defined on a simply connected open set, has no crumpled points, and any two of its points are joined by a curve of finite length inside it. For a tame crease pattern a local flat folding is again determined up to rigid motion.

## Depends on

None.

## Proof depends on

None.

## Expansion

Tameness is what makes infinite crease patterns tractable: a finite-length curve crosses only finitely many creases, so composing finitely many reflections propagates a local folding from one crease to any other, and, by König's lemma, a tame crease pattern with a local flat folding is flat-foldable exactly when the neighborhood of every finite set of its creases is.

## Sources

- David Eppstein, "Computational Complexities of Folding", Journal of Information Processing 33, pp. 954–973, 2025, <https://doi.org/10.2197/ipsjjip.33.954>; read in arXiv:2410.07666v1, <https://arxiv.org/abs/2410.07666v1>: Section 2 ("Preliminaries: Finite and infinite flat foldings": local flat foldings, layerings, flat foldings and uncrossed layerings) and Section 6.1 ("Fundamentals": tame crease patterns), in the numbering of that version.
