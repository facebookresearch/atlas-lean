# Inserting a point into a left-endpoint sum

For a finite set $P \subseteq \mathbb{R}$, let $\operatorname{prev}_P(x)$ be the largest element of $P$ below $x$ (or $x$ if there is none), and let the left-endpoint sum of $f$ against $h$ be $\sum_{x \in P} f(\operatorname{prev}_P(x))\,(h(x) - h(\operatorname{prev}_P(x)))$. Let $p \notin P$, let $v \in P$ be the least element of $P$ above $p$, and suppose $P$ has an element below $p$, so $p$ lies in the cell $(u, v]$ with $u = \operatorname{prev}_P(p)$. Inserting $p$ changes the left-endpoint sum by $(f(p) - f(u))(h(v) - h(p))$.
