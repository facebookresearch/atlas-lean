# Partial mass balance

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The survival mass $s_n(q)$ is defined by recursion on $n$: $s_0(q) = 1$ and

$$s_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, s_n(q^{a}).$$

The termination mass $\mathrm{stop}_n(q)$ is defined by recursion on $n$: $\mathrm{stop}_0(q) = q_{[\,]}(\bot)$ and

$$\mathrm{stop}_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, \mathrm{stop}_n(q^{a}).$$

Then for every $N \in \mathbb{N}$,

$$\sum_{k=0}^{N-1} \mathrm{stop}_k(q) + s_N(q) = 1.$$

The mass of all terminated strings with fewer than $N$ ordinary tokens plus the mass of surviving to length $N$ is exactly one; nothing is lost and nothing is renormalized at any finite horizon.
