# Terminated Mass eq law eos Lift

Let $T$ be a finite set of ordinary tokens and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$; no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

Let $\hat q$ be the EOS-lifted kernel on words over $T \cup \{\bot\}$, $\hat q_u = q_{\pi(u)}$, where $\pi(u)$ deletes every $\bot$ from $u$. For a kernel $p$ on an alphabet $A$, let $P^{p}_n$ be the distribution of the length-$n$ word obtained by drawing each symbol from $p$ at the current prefix: $P^{p}_0$ is the point mass at $[\,]$, and a word $u_1 \cdots u_n$ has mass $P^{p}_n(u_1 \cdots u_n) = \prod_{i=1}^{n} p_{u_1 \cdots u_{i-1}}(u_i)$. For a word $w$ over $T$, write $\iota(w)$ for the same word read over $T \cup \{\bot\}$.

Let $M_q(w) = S_q(w)\, q_w(\bot)$ be the terminated mass of $w$, where $S_q(a_1 \cdots a_n) = \prod_{i=1}^{n} q_{a_1 \cdots a_{i-1}}(a_i)$ (and $S_q([\,]) = 1$). Then for every finite word $w$ over $T$,

$$M_q(w) = P^{\hat q}_{|w| + 1}\big(\iota(w)\,\bot\big),$$

the mass of the word $w$ followed by $\bot$. Every proper prefix of $\iota(w)\,\bot$ contains no $\bot$.
