# Composition of submersions

Let $\mathbb{K}$ be a nontrivially normed field, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be $C^n$ manifolds without
boundary over $\mathbb{K}$ modelled on Banach spaces. If $f : M \to N$ and $g : N \to N'$ are
$C^n$ submersions, then so is $g \circ f$. Here $f$ is a $C^n$ submersion when there is one normed
space $F$ such that at every $x \in M$ there are charts of the $C^n$ maximal atlases around $x$ and
$f(x)$, the first mapped by $f$ into the second, in which $f$ reads $(u, v) \mapsto u$ after a
continuous linear identification of the model space of $M$ with the product of the model space of
$N$ and $F$.

Proof: Apply the complement-level pointwise composition theorem using the two fixed global
complements, then package their product as the complement of the composite.

## Sources

- Mathlib `Mathlib/Geometry/Manifold/Submersion.lean` TODO (`IsSubmersion.comp`); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
