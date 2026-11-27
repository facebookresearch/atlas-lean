# Face walk along a boundary orbit

Let $K \subseteq \mathbb{Z}^2$. A boundary dart of $K$ is a [dart](exit-dart.md) whose tail lies in $K$ and whose head does not. The successor $\sigma(e)$ of a boundary dart $e$ with tail $t$, head $h$ and direction $u = h - t$ is defined as follows, with $r = (u_2, -u_1)$ the direction $u$ rotated clockwise by a quarter turn:

- if $h + r \in K$, $\sigma(e)$ is the dart from $h + r$ to $h$;
- otherwise, if $t + r \in K$, $\sigma(e)$ is the dart from $t + r$ to $h + r$;
- otherwise $\sigma(e)$ is the dart from $t$ to $t + r$.

The successor of a boundary dart is again a boundary dart. For $n \in \mathbb{N}$, the face walk along the boundary orbit of $e$ is the walk in the face-boundary graph of $K$ (see [anchored dual cycles](anchored-cycle-exists.md)) through the [faces to the left](dart-face.md) of $e, \sigma(e), \dots, \sigma^n(e)$.
