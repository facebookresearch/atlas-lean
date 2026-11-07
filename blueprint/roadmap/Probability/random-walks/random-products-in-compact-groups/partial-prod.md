# Successive products along a coin sequence

Let $G$ be a group, let $\varphi, \psi \in G$,
and let $c : \mathbb{N} \to \{\mathrm{false}, \mathrm{true}\}$. For $i \ge 1$ let $f_i$ be the
generator chosen at index $i - 1$: $f_i = \varphi$ if $c(i - 1) = \mathrm{false}$ and
$f_i = \psi$ if $c(i - 1) = \mathrm{true}$. The successive products are defined by $P_0 = 1$
and $P_{n+1} = P_n f_{n+1}$, so $P_n = f_1 f_2 \cdots f_n$ for every $n \in \mathbb{N}$, with
$P_0$ the empty product.

The typescript writes the terms as $f_1, f_1(f_2), f_1(f_2 f_3), \ldots$, read as successive
products.
