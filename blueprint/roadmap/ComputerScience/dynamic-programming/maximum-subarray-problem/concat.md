# Maximum suffix sum after appending an element

Let $\alpha$ be an additive monoid with a
linear order such that $a \le b$ implies $a + c \le b + c$. If $e$ is the maximum sum of a
nonempty suffix of a list $p$ over $\alpha$, then for every $x \in \alpha$ the maximum sum of a
nonempty suffix of the list obtained by appending $x$ to $p$ is $\max(x, e + x)$.

Such a suffix is either $[x]$ alone or a nonempty suffix of $p$ followed by $x$.
