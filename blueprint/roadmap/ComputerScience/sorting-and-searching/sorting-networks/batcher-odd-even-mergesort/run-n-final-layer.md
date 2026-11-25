# Output of the last layer of the odd-even merger

Let $\alpha$ be a linearly ordered type,
$k \in \mathbb{N}$ and $f : \mathbb{N} \to \alpha$ an assignment of values to the wires. Running
the final layer for $k$ on $f$ gives at a wire $x$ the value $\min(f(x), f(x + 1))$ if $x$ is
odd and $\lfloor x / 2 \rfloor < 2^{k+1} - 1$; otherwise the value $\max(f(x - 1), f(x))$ if
$x$ is even, $x > 0$ and $(x - 2) / 2 < 2^{k+1} - 1$; and the value $f(x)$ in all other cases.
In other words, for each $i < 2^{k+1} - 1$ wire $2i + 1$ receives the minimum and wire $2i + 2$
the maximum of the values of $f$ on these two wires, and every other wire keeps its value.
