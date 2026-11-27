# Weak approximation for absolute values

Let $K$ be a field and let
$(v_i)_{i \in \iota}$ be a finite family of absolute values $v_i : K \to \mathbb R$, each
nontrivial ($v_i(y) \ne 1$ for some nonzero $y \in K$), that are pairwise inequivalent: for
$i \ne j$, $v_i$ and $v_j$ are not equivalent, where $v$ and $w$ are equivalent when
$v(x) \le v(y) \iff w(x) \le w(y)$ for all $x, y \in K$. Then for every family
$(a_i)_{i \in \iota}$ of elements of $K$ and every real $\varepsilon > 0$ there is $x \in K$
with $v_i(x - a_i) < \varepsilon$ for every $i \in \iota$.

This is the $\varepsilon$-form of `AbsoluteValue.denseRange_algebraMap_pi`: the diagonal image of
$K$ is dense in the product over $i$ of $K$ with the topology of $v_i$.
