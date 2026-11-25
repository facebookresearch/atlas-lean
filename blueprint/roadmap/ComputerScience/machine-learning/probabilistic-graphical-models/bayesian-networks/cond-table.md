# The conditional law of a node given its parents

Let $\alpha$ be a finite nonempty type with a fixed element $a_0$, let
$P : \alpha^n \to \mathbb{R}$ with $P(x) \ge 0$ for all $x$, and let
$\mathrm{pa}(k) \subseteq \{0, \dots, k - 1\}$ be parent sets. Write $P(x_U)$ for the sum of $P(y)$
over the configurations $y$ that agree with $x$ on $U$. For a node $k$ and values $z$ of its
parents, let $x^z \in \alpha^n$ be the [extension](extend-pa.md) of $z$ (equal to $z$ on the
parents of $k$ and to $a_0$ elsewhere). The table of $P$ at $k$ and $z$ is the point mass at
$a_0$ if $P(x^z_{\mathrm{pa}(k)}) = 0$, and otherwise the distribution

$$a \mapsto \frac{P\big((x^z[k \mapsto a])_{\{k\} \cup \mathrm{pa}(k)}\big)}{P(x^z_{\mathrm{pa}(k)})},$$

where $x^z[k \mapsto a]$ is $x^z$ with value $a$ at node $k$: the conditional law of node $k$
given its parents take the values $z$.
