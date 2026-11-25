# Survival Mass eq tsum law eos Lift

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The survival mass $s_n(q)$ is defined by recursion on $n$: $s_0(q) = 1$ and

$$s_{n+1}(q) = \sum_{a \in T} q_{[\,]}(a)\, s_n(q^{a}).$$

Let $\hat q$ be the EOS-lifted kernel on words over $T \cup \{\bot\}$, $\hat q_u = q_{\pi(u)}$, where $\pi(u)$ deletes every $\bot$ from $u$. For a kernel $p$ on an alphabet $A$, let $P^{p}_n$ be the distribution of the length-$n$ word obtained by drawing each symbol from $p$ at the current prefix: $P^{p}_0$ is the point mass at $[\,]$, and a word $u_1 \cdots u_n$ has mass $P^{p}_n(u_1 \cdots u_n) = \prod_{i=1}^{n} p_{u_1 \cdots u_{i-1}}(u_i)$. For a word $w$ over $T$, write $\iota(w)$ for the same word read over $T \cup \{\bot\}$.

Then for every $n \in \mathbb{N}$,

$$s_n(q) = \sum_{w \in T^n} P^{\hat q}_n\big(\iota(w)\big),$$

the sum over all words over $T$ of length exactly $n$.
