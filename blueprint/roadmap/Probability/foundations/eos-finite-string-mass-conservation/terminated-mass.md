# Terminated mass of a finite word

Let $T$ be any set of ordinary tokens, finite or infinite, and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$ (an unordered sum of a summable family; a finite sum when $T$ is finite); no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The terminated mass of a word $w$ over $T$ is

$$M_q(w) = S_q(w)\, q_w(\bot),$$

where $S_q([\,]) = 1$ and $S_q(a_1 \cdots a_n) = \prod_{i=1}^{n} q_{a_1 \cdots a_{i-1}}(a_i)$. It is the probability of emitting exactly the ordinary tokens of $w$, in order, and then $\bot$ at prefix $w$. These masses live on finite words only; the mass of never terminating is not renormalized into them.
