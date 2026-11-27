# Runtime head communication advances or keeps the interface

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ a semantically compatible
ownership context, $a$, $b$ names and $p$, $q$ processes with $\Gamma; \Delta \vdash_n
\overline{a}\langle b\rangle.p \mid a(\cdot).q$. Then there is a semantically compatible ownership
context $\Xi$ with $\Gamma; \Xi \vdash_n p \mid q\{b\}$ such that $\Xi = \Delta$ (a service
invocation) or $\Xi$ is a semantic advance of $\Delta$ (a linear communication).
