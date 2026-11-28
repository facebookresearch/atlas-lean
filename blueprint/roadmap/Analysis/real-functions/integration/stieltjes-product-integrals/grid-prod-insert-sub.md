# Change of a grid product under an interior insertion

For a finite set $P \subseteq \mathbb{R}$, let $\operatorname{prev}_P(x)$ be the largest element of $P$ below $x$ (or $x$ if there is none), and let the grid product of $A$ over $P$ be $\prod_{x \in P} \big(1 + A(x) - A(\operatorname{prev}_P(x))\big)$. Let $p \notin P$, let $v \in P$ be the least element of $P$ above $p$, and suppose $P$ has an element below $p$. Then

$$\operatorname{GP}_{P \cup \{p\}}(A) - \operatorname{GP}_P(A) = \Big(\prod_{x \in P \setminus \{v\}} \big(1 + A(x) - A(\operatorname{prev}_P(x))\big)\Big)\, \big(A(p) - A(\operatorname{prev}_P(p))\big)\big(A(v) - A(p)\big).$$
