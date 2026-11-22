# Inversion of runtime typing for parallel composition

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$,
$q$ processes. If $\Gamma; \Delta \vdash_n p \mid q$, then there are ownership contexts $\Theta$,
$\Xi$ with disjoint domains such that $\Delta = \Theta \cup \Xi$, $\Gamma; \Theta \vdash_n p$ and
$\Gamma; \Xi \vdash_n q$.
