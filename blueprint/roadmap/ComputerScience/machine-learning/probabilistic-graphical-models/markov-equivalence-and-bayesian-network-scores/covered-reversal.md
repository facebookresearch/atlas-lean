# Covered-edge reversal

Let $\mathrm{Pa}$ and $\mathrm{Pa}'$ be structures on a set $V$, assigning to each vertex a finite
set of parents. Then $\mathrm{Pa}'$ is obtained from $\mathrm{Pa}$ by reversing a covered edge
$x \to y$ (Chickering 1995) if $x \ne y$, $\mathrm{Pa}(y) = \mathrm{Pa}(x) \cup \{x\}$ (so $x$ is a
parent of $y$ and the other parents of $y$ are exactly the parents of $x$), and after the reversal
$y$ has parents $\mathrm{Pa}(x)$, $x$ has parents $\mathrm{Pa}(x) \cup \{y\}$, and every other
vertex keeps its parents. Acyclicity is not required: the score identity holds for any parent-set
maps (on a DAG, $x \notin \mathrm{Pa}(x)$ and $y \notin \mathrm{Pa}(x)$ hold automatically).
