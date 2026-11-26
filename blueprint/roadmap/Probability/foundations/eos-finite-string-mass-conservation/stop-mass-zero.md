# Stop Mass zero

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The termination mass at length zero is the EOS probability at the empty prefix:

$$\mathrm{stop}_0(q) = q_{[\,]}(\bot),$$

where $\mathrm{stop}_n(q)$ is defined by this value at $n = 0$ and $\mathrm{stop}_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, \mathrm{stop}_n(q^{a})$.
