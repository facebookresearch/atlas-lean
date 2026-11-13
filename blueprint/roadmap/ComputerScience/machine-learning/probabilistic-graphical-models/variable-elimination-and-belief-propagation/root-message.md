# Root message of a tree model

Let $\alpha$ be finite. The root message of a pairwise tree
model $m$ on the vertices $0, \dots, n$ is the function $r_m : \alpha \to \mathbb{R}$ defined by
recursion on $n$: if $n = 0$, it is the unary factor of the root $0$; if $m$ is a model on the
vertices $0, \dots, n + 1$, it is $r_{m'}$, where $m'$ is the model on the vertices $0, \dots, n$
obtained from $m$ by eliminating the last vertex.

By variable elimination, $r_m(a)$ is the unnormalized marginal of the root at $a$.
