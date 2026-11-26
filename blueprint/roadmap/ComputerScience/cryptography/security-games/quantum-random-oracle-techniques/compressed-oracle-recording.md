# Recording quantum queries: the database explains the adversary's output

Let $\mathcal{A}$ make $q$ queries to a random oracle and output $(x_1,\dots,x_k,y_1,\dots,y_k)$, and let $R$ be a relation on these together with oracle values. Measure the compressed oracle's database $D$ after $\mathcal{A}$ finishes. Then

$$
\sqrt{\Pr[\mathcal{A}\text{ outputs a tuple with }y_i=H(x_i)\ \forall i\text{ and }R]}\le\sqrt{\Pr[D\text{ contains a tuple satisfying }R]}+\sqrt{k/2^{m}}.
$$

Hence bounding the probability that a $q$-query evolution of the database reaches a "good" database bounds the adversary's success, and each query changes the database's good-amplitude by a controlled amount (typically $O(\sqrt{q/2^{m}})$ or $O(\sqrt{k/2^{m}})$ per query, depending on the relation).

## Proof sketch

The compressed and uncompressed purified oracles are related by an isometry commuting with the adversary's operations, so the final states correspond. For an output pair $(x_i,y_i)$, if $x_i\notin D$ then $H(x_i)$ is uniform conditioned on the joint state, contributing $2^{-m}$ per pair; otherwise the database already records a value. A triangle inequality on amplitudes gives the stated bound.

## Depends on

- [Zhandry's compressed oracle representation](compressed-oracle.md)

## Sources

- Mark Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO (2019), IACR ePrint 2018/276.
