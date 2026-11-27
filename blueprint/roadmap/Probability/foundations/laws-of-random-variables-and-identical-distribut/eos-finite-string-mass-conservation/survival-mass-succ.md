# Survival mass and its one-step recursion

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The survival mass $s_n(q)$ is defined by recursion on $n$: $s_0(q) = 1$ and, for every $n \in \mathbb N$,

$$s_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, s_n(q^{a}),$$

where $q_{[\,]}(a)$ is the probability that the first symbol is the token $a$. It is the total mass of ordinary words of length exactly $n$, that is, the probability of not having emitted $\bot$ in the first $n$ steps.
