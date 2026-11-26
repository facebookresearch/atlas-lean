# Survival Mass le pow of uniform EOS

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The survival mass $s_n(q)$ is defined by recursion on $n$: $s_0(q) = 1$ and

$$s_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, s_n(q^{a}).$$

Let $\varepsilon \in [0, \infty]$ satisfy $\varepsilon \le q_w(\bot)$ for every finite word $w$ over $T$ (this forces $\varepsilon \le 1$; $1 - \varepsilon$ denotes truncated subtraction in $[0,\infty]$). No positivity of $\varepsilon$ is needed. Then for every $n \in \mathbb{N}$,

$$s_n(q) \le (1 - \varepsilon)^n.$$
