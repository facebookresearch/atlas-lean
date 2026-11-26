# One round of naive partition refinement for strong bisimilarity

Let $L$ be a labelled transition system with states $S$ and labels $\Lambda$, given by its transition relation $s \xrightarrow{\mu} t$. For a relation $R$ on $S$, one refinement round produces the relation $R'$ on $S$ with $a \mathrel{R'} b$ exactly when $a \mathrel{R} b$ and, for every label $\mu$:

- every transition $a \xrightarrow{\mu} a'$ is matched by some transition $b \xrightarrow{\mu} b'$ with $a' \mathrel{R} b'$, and
- every transition $b \xrightarrow{\mu} b'$ is matched by some transition $a \xrightarrow{\mu} a'$ with $a' \mathrel{R} b'$.

So $R' \subseteq R$ for every $R$.
