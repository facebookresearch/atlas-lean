# Ambainis: relational adversary bound for non-Boolean input alphabets

Let $f : D \to \beta$ with $D \subseteq \Sigma^N$ and $\beta$ finite, where the symbols of the finite alphabet $\Sigma$ are encoded as bit strings of a fixed length and queried through the value oracle $|i, a, w\rangle \mapsto |i, a \oplus x_i, w\rangle$. Let $X, Y \subseteq D$ be sets of inputs with $f(x) \ne f(y)$ for every $x \in X$ and every $y \in Y$, and let $R \subseteq X \times Y$ be such that every $x \in X$ is related to at least $m$ inputs $y \in Y$ and every $y \in Y$ to at least $m'$ inputs $x \in X$. For $(x, y) \in R$ and an index $i$ let $\ell_{x,i}$ be the number of $y' \in Y$ with $(x, y') \in R$ and $y'_i \ne x_i$, and $\ell'_{y,i}$ the number of $x' \in X$ with $(x', y) \in R$ and $x'_i \ne y_i$, and let $L$ be the maximum of $\ell_{x,i}\ell'_{y,i}$ over all $(x, y) \in R$ and all $i$ with $x_i \ne y_i$. Then for every fixed error $0 \le \varepsilon < 1/2$, every quantum query algorithm computing $f$ with error at most $\varepsilon$ on every input of $D$ makes

$$Q_\varepsilon(f) = \Omega\Big(\sqrt{mm'/L}\Big)$$

queries.

## Proof sketch

Run the algorithm on the superposition giving weight $1/\sqrt{2|X|}$ to each $x \in X$ and $1/\sqrt{2|Y|}$ to each $y \in Y$, and track $S_t = \sum_{(x,y) \in R} |(\rho_t)_{xy}|$ for the reduced density matrix $\rho_t$ on the input register after $t$ queries. Distinguishing $f(x) \ne f(y)$ with error $\varepsilon$ forces $S_0 - S_T \ge (1 - 2\sqrt{\varepsilon(1-\varepsilon)}) S_0$. One query changes only entries with $x_i \ne y_i$ for the queried $i$, and positive semidefiniteness with the weights $\sqrt{\ell'_{y,i}/\ell_{x,i}}$ bounds the change per query by $\sqrt{L}$; since $X$ and $Y$ are disjoint (no input lies in both, as $f(x) \ne f(y)$), the diagonal of $\rho$ over $X \cup Y$ has trace one. (Derived, not stated by Ambainis: since $|R| \ge \max(m|X|, m'|Y|) \ge \sqrt{mm'|X||Y|}$, $S_0 \ge \sqrt{mm'}/2$, and the argument gives the explicit form $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\sqrt{mm'} \le 2T\sqrt{L}$ for every $T$-query algorithm.)

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Proceedings of the 32nd ACM Symposium on Theory of Computing (STOC 2000); journal version Journal of Computer and System Sciences 64(4), 2002; arXiv:quant-ph/0002066: Section 2 (the oracle and its extension to larger alphabets) and Theorem 6 with its proof.
