# Ambainis: relational adversary bound for non-Boolean input alphabets

Let $f : D \to \beta$ with $D \subseteq \Sigma^N$, and let $R \subseteq D \times D$ be a nonempty relation between inputs with $f(x) \ne f(y)$. Suppose every $x$ in the left projection is related to at least $m$ inputs, every $y$ in the right projection to at least $m'$ inputs, and for every related pair $(x, y)$ and index $i$ with $x_i \ne y_i$, the product $\ell_{x,i} \ell'_{y,i}$ is at most $L$, where $\ell_{x,i}$ is the number of partners $y'$ of $x$ with $y'_i \ne x_i$ and $\ell'_{y,i}$ the number of partners $x'$ of $y$ with $x'_i \ne y_i$. Then every $T$-query value-oracle algorithm computing $f$ with error $\varepsilon$ satisfies

$$\big(1 - 2\sqrt{\varepsilon(1 - \varepsilon)}\big)\sqrt{m m'} \le 2T\sqrt{L}.$$

Ambainis states this (Theorem 6) for the standard oracle $|i, a\rangle \mapsto |i, a \oplus x_i\rangle$ and an $\Omega(\sqrt{mm'/L})$ conclusion; his proof gives the displayed constant and uses only that the oracle acts on the query and value registers by a unitary depending on $x_i$ alone, so it holds verbatim for any unitary oracle family $\mathrm{step} : \Sigma \to U(\mathbb{C}^V)$ and any finite set of outcomes.

## Proof sketch

Run the algorithm on the superposition of inputs giving weight $1/\sqrt{2|X|}$ to each left input and $1/\sqrt{2|Y|}$ to each right input, and track $S_t = \sum_{(x,y) \in R} |(\rho_t)_{xy}|$ for the reduced density matrix $\rho_t$ on the input register. Then $S_0 \ge \sqrt{mm'}/2$, and distinguishing $f(x) \ne f(y)$ with error $\varepsilon$ forces $S_0 - S_T \ge (1 - 2\sqrt{\varepsilon(1-\varepsilon)}) S_0$. One query changes only entries with $x_i \ne y_i$ for the queried $i$, and positive semidefiniteness with the weights $\sqrt{\ell'_{y,i}/\ell_{x,i}}$ bounds the change per query by $\sqrt{L}$.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002, Lemma 1 and Theorem 6 with its proof.
