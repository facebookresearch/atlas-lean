# Satisfaction in the modal μ-calculus

Let $M$ be a Kripke model with accessibility
relation $R$ and valuation $V$, and let $\rho$ be an environment assigning a set of worlds to
each variable index $n \in \mathbb{N}$. For a set of worlds $S$, write $\rho[0 \mapsto S]$ for the
environment sending index $0$ to $S$ and index $n + 1$ to $\rho(n)$. The set $[\![\varphi]\!]_\rho$
of worlds satisfying a formula $\varphi$ in $M$ under $\rho$ is defined by recursion on
$\varphi$: an atom $a$ holds at $w$ when $V$ makes $a$ true at $w$, and the negated atom of $a$
when $V$ does not; the variable with index $n$ denotes $\rho(n)$; $\bot$ holds nowhere and $\top$
everywhere; conjunction and disjunction denote intersection and union; $\Box\varphi$ holds at $w$
when $\varphi$ holds at every $v$ with $w \mathrel{R} v$, and $\Diamond\varphi$ when $\varphi$
holds at some such $v$; $\mu\varphi$ holds at $w$ when $w \in S$ for every set of worlds $S$ with
$[\![\varphi]\!]_{\rho[0 \mapsto S]} \subseteq S$; and $\nu\varphi$ holds at $w$ when $w \in S$
for some set of worlds $S$ with $S \subseteq [\![\varphi]\!]_{\rho[0 \mapsto S]}$.

So $\mu\varphi$ is the least pre-fixed point of $S \mapsto [\![\varphi]\!]_{\rho[0 \mapsto S]}$,
stated directly as an infimum over pre-fixed points, and $\nu\varphi$ is the greatest
post-fixed point, stated as a supremum over post-fixed points.
