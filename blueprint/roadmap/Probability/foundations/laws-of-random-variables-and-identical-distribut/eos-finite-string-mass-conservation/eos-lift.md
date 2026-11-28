# EOS-lift of a next-step kernel

Let $T$ be any set of ordinary tokens, finite or infinite, and let $\bot$ denote the end-of-string symbol (EOS). A next-step kernel $q$ assigns to every finite word $w$ over $T$ a probability distribution $q_w$ on $T \cup \{\bot\}$, so that $q_w(\bot) + \sum_{a \in T} q_w(a) = 1$ (an unordered sum of a summable family; a finite sum when $T$ is finite); no positivity of $q_w(\bot)$ is assumed, and it may depend on the whole prefix $w$. For $a \in T$ the shifted kernel $q^{a}$ is given by $q^{a}_w = q_{aw}$, where $aw$ is the word $a$ followed by $w$, and $[\,]$ is the empty word. All masses below take values in $[0, \infty]$.

The EOS-lift of $q$ is the kernel $\hat q$ on finite words over $T \cup \{\bot\}$ given by

$$\hat q_u = q_{\pi(u)},$$

where $\pi(u)$ is the word over $T$ obtained from $u$ by deleting every occurrence of $\bot$. In particular, on a word with no $\bot$ it agrees with $q$ at the corresponding ordinary prefix.
