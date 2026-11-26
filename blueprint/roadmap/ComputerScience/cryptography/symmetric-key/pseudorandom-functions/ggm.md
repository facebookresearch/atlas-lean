# The GGM tree construction

Let $G : S \to S \times S$ be a length-doubling generator and
write $G(s) = (G_0(s), G_1(s))$. The keyed function $F : S \times \{0,1\}^\ell \to S$ of
Goldreich, Goldwasser and Micali is
$F(k, x_1 \cdots x_\ell) = G_{x_\ell}(\cdots G_{x_2}(G_{x_1}(k)) \cdots)$: the label of the leaf
addressed by $x$ in the binary tree of depth $\ell$ whose root is labelled $k$ and in which the
children of a node labelled $t$ are labelled $G_0(t)$ and $G_1(t)$. A bit string
$x_1 \cdots x_\ell$ is given as the function on $\{0, \dots, \ell - 1\}$ that maps $i$ to
$x_{i+1}$.
