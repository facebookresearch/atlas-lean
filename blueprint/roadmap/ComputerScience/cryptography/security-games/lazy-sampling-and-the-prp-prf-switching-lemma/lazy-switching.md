# Lazy switching lemma

Let $D$ be a finite nonempty set with $N$ elements, $T$ a table on $D$ with $m$ unused values, and $c$
an adaptive distinguisher with oracle $D \to D$ that makes at most $q$ queries. Started from $T$, the
lazy random function and the lazy random permutation are distinguished by $c$ with advantage at most

$$1 - \frac{m(m - 1) \cdots (m - q + 1)}{N^q}.$$

The two oracles answer a fresh query alike unless the random function hits a used value, so the runs
are identical until that bad event.
