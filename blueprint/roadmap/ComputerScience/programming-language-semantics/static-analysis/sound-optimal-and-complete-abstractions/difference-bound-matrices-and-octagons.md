# Difference-bound matrices and octagons

Let $\mathbb{I}$ be $\mathbb{Z}$, $\mathbb{Q}$ or $\mathbb{R}$, and let $V = \{v_0, \dots, v_{N-1}\}$ be a finite set of variables. Variables take values in $\mathbb{I}$; bounds take values in $\mathbb{I} \cup \{+\infty\}$.

- **Difference-bound matrices.** A set of *potential constraints* $v_j - v_i \le c$ with at most one constraint per ordered pair is represented by an $N \times N$ *difference-bound matrix* (DBM) $m$ with entries in $\mathbb{I} \cup \{+\infty\}$, $m_{ij} = c$ if $v_j - v_i \le c$ is a constraint and $m_{ij} = +\infty$ otherwise. Its *potential graph* $G(m)$ has an edge $v_i \to v_j$ of weight $m_{ij}$ whenever $m_{ij} < +\infty$. Its *domain* is $D(m) = \{s \in \mathbb{I}^N \mid \forall i, j.\ s_j - s_i \le m_{ij}\}$. DBMs are ordered pointwise, $m \trianglelefteq n$ if $m_{ij} \le n_{ij}$ for all $i, j$; then $m \trianglelefteq n$ implies $D(m) \subseteq D(n)$, but not conversely, and different DBMs can have the same domain.
- **Octagons.** To represent constraints $\pm v_i \pm v_j \le c$ over $V^+ = \{v_0, \dots, v_{N-1}\}$, each variable $v_i$ gets a positive form $v_i^+$ and a negative form $v_i^-$, standing for $+v_i$ and $-v_i$, with indices $2i$ and $2i + 1$, and constraints become potential constraints over these $2N$ forms: $v_i + v_j \le c$ becomes $v_i^+ - v_j^- \le c$ and $v_j^+ - v_i^- \le c$, and $v_i \le c$ becomes $v_i^+ - v_i^- \le 2c$, and similarly for the other sign patterns. Writing $\bar\imath$ for the index of the opposite form of index $i$, a $2N \times 2N$ DBM $m^+$ is *coherent* if $m^+_{ij} = m^+_{\bar\jmath\,\bar\imath}$ for all $i, j$. Its *octagon* is

    $$D^+(m^+) = \{(s_0, \dots, s_{N-1}) \in \mathbb{I}^N \mid (s_0, -s_0, \dots, s_{N-1}, -s_{N-1}) \in D(m^+)\},$$

    and an *octagon* is any set of this form for a coherent $m^+$.

Octagons express invariants such as $-i + 1 \le a \le i - 1$, which interval analysis cannot, with memory quadratic in the number of variables.

## Sources

- A. Miné, "The octagon abstract domain", *Proceedings of the Eighth Working Conference on Reverse Engineering (WCRE 2001)*, IEEE, 2001, pp. 310–319, doi:10.1109/WCRE.2001.957836, author copy <https://arxiv.org/abs/cs/0703084>: Section III (potential constraints and DBMs, the potential graph, the order $\trianglelefteq$, the domain $D(m)$ and Remark 1, Figure 4) and Section IV (representing sums by positive and negative forms, Figure 5, the index notation $\bar\imath$, coherence and Theorem 1, and the definition of $D^+(m^+)$ and of octagons); the introduction and Figure 1 for the motivating invariant.
