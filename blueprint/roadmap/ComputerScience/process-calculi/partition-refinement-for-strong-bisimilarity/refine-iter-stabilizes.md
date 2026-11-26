# Naive partition refinement stabilizes after as many rounds as there are states

Let $L$ be a labelled transition system with states $S$ and labels $\Lambda$, given by its transition relation $s \xrightarrow{\mu} t$. The refinement iterates are the relations $\equiv_k$ on $S$ with $\equiv_0$ the total relation (every pair of states related) and $a \equiv_{k+1} b$ exactly when $a \equiv_k b$ and, for every label $\mu$, every transition $a \xrightarrow{\mu} a'$ is matched by some $b \xrightarrow{\mu} b'$ with $a' \equiv_k b'$, and every transition $b \xrightarrow{\mu} b'$ is matched by some $a \xrightarrow{\mu} a'$ with $a' \equiv_k b'$. Assume $S$ is finite with $N$ elements; the label type $\Lambda$ is arbitrary (it need not be finite, and $L$ need not be finitely branching). Then the iterates at rounds $N$ and $N + 1$ coincide: for all states $a, b$,

$$a \equiv_{N+1} b \iff a \equiv_N b.$$
