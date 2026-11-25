# Positive spanning sets and first-order form closure

For vectors $a_1, \dots, a_j \in \mathbb{R}^n$ let $F = [a_1 \cdots a_j] \in \mathbb{R}^{n \times j}$ and let $\operatorname{pos}(a_1, \dots, a_j) = \{\sum_i k_i a_i : k_i \ge 0\}$ be their positive span. Then:

1. **Linear test.** $\operatorname{pos}(a_1, \dots, a_j) = \mathbb{R}^n$ if and only if $\operatorname{rank} F = n$ and $Fk = 0$ for some $k$ with every $k_i > 0$.
2. **Dual test.** $\operatorname{pos}(a_1, \dots, a_j) = \mathbb{R}^n$ if and only if the only $c \in \mathbb{R}^n$ with $a_i^\top c \ge 0$ for every $i$ is $c = 0$.
3. **Counting.** If $\operatorname{pos}(a_1, \dots, a_j) = \mathbb{R}^n$ then $j \ge n + 1$, and $n + 1$ vectors suffice: $e_1, \dots, e_n, -(e_1 + \dots + e_n)$.

In grasping, a body touched at stationary frictionless point contacts with contact wrenches $\mathcal{F}_1, \dots, \mathcal{F}_j$ admits only the twists $\mathcal{V}$ with $\mathcal{F}_i^\top\mathcal{V} \ge 0$ to first order, and it is in **first-order form closure** when only $\mathcal{V} = 0$ is admitted. By part 2 this means $\operatorname{pos}(\mathcal{F}_1, \dots, \mathcal{F}_j)$ is the whole wrench space, $\mathbb{R}^3$ for planar and $\mathbb{R}^6$ for spatial bodies, and by part 3 at least $4$ contacts are needed for a planar body and $7$ for a spatial one.

**Proof.** For part 1, if the positive span is everything then so is the linear span, so $\operatorname{rank} F = n$, and writing $-\sum_i a_i = \sum_i k_i a_i$ with $k_i \ge 0$ gives $F(\mathbf{1} + k) = 0$ with positive coefficients. Conversely, any $v = Fc$ for some $c$ by the rank condition, and $v = F(c + tk)$ with $c + tk \ge 0$ for large $t$. For part 2, if the positive span is everything and $a_i^\top c \ge 0$ for all $i$, then $x^\top c \ge 0$ for every $x$, in particular for $x = -c$, so $c = 0$. If the positive span is a proper subset, it is a closed convex cone (finitely generated cones are closed), and separating a point outside it gives $c \ne 0$ with $x^\top c \ge 0$ on the cone, in particular $a_i^\top c \ge 0$. For part 3, part 1 needs $j \ge n$, and $j = n$ is impossible because then $F$ is invertible and $Fk = 0$ forces $k = 0$; the displayed $n + 1$ vectors satisfy part 1 with $k = \mathbf{1}$.

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Chapter 12: Definition 12.1 (linear, positive and convex spans) and fact 2, that $\mathbb{R}^n$ can be positively spanned by $n + 1$ vectors but no fewer (pp. 462–463); Section 12.1.7, first-order form closure as $\operatorname{pos}(\{\mathcal{F}_1, \dots, \mathcal{F}_j\}) = \mathbb{R}^6$ and the counts of $4$ and $7$ contacts (pp. 478–479), and the linear programming test (12.14), full rank and $Fk = 0$ with $k > 0$ (p. 480). The proofs are on the page.
