# Stop Mass eq tsum terminated

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The termination mass $\mathrm{stop}_n(q)$ is defined by recursion on $n$: $\mathrm{stop}_0(q) = q_{[\,]}(\bot)$ and

$$\mathrm{stop}_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, \mathrm{stop}_n(q^{a}).$$

Let $M_q(w) = S_q(w)\, q_w(\bot)$ be the terminated mass of $w$, where $S_q(a_1 \cdots a_n) = \prod_{i=1}^{n} q_{a_1 \cdots a_{i-1}}(a_i)$ (and $S_q([\,]) = 1$). Then for every $n \in \mathbb{N}$,

$$\mathrm{stop}_n(q) = \sum_{w \in T^n} M_q(w),$$

the sum over all words over $T$ of length exactly $n$.
