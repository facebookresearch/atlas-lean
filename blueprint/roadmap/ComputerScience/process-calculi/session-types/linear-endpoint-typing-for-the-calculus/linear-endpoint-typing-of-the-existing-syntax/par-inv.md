# Inversion of endpoint typing for parallel composition

Let $n$ be a natural number, $\Delta$ an ownership context and $p$, $q$ processes. If $\Delta
\vdash_n p \mid q$, then there are ownership contexts $\Theta$, $\Xi$ with disjoint domains such
that $\Delta = \Theta \cup \Xi$, $\Theta \vdash_n p$ and $\Xi \vdash_n q$.
