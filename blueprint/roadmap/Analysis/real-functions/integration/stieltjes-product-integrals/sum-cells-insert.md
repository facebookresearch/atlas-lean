# Cell sums after inserting a point

For a finite set $P \subseteq \mathbb{R}$ let $\operatorname{prev}_P(x)$ be the largest element of $P$ below $x$ (or $x$ if there is none). Let $p \notin P$, let $v \in P$ be the least element of $P$ above $p$, and suppose $P$ has an element below $p$. For every $\psi : \mathbb{R}^2 \to \mathbb{R}$,

$$\sum_{x \in P \cup \{p\}} \psi(\operatorname{prev}_{P \cup \{p\}}(x), x) = \sum_{x \in P \setminus \{v\}} \psi(\operatorname{prev}_P(x), x) + \psi(\operatorname{prev}_P(p), p) + \psi(p, v).$$
