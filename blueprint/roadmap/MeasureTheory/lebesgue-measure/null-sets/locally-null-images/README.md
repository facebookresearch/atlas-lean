# Sets with locally null image have null image

Let $X$ be a second-countable topological space, $\mu$ a measure on a measurable space $Y$,
$f : X \to Y$ a function and $s \subseteq X$. If every point of $s$ has a neighbourhood $V$ with
$\mu(f(V \cap s)) = 0$, then $\mu(f(s)) = 0$. Here $\mu$ is evaluated as an outer measure, so the
images need not be measurable.

## Idea

Being null is a local property of images. The interiors of the neighbourhoods $V$ cover $s$, and in
a second-countable space every such cover has a countable subcover, so $f(s)$ is a countable union of
sets $f(V_k \cap s)$ of outer measure $0$, which has outer measure $0$ by countable subadditivity. A
typical use is to show that a map sends null sets to null sets by checking it near each point, where
the map may be Lipschitz.

## Statements

- [Sets with locally null image have null image](measure-image-null-of-locally-null.md)
