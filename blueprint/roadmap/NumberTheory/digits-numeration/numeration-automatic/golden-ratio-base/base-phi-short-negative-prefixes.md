# Short prefixes of the negative parts of base phi expansions

Let $\varphi$ be the golden
ratio. For integers $p, q, r$ let $V(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 1\}$
and $V_0(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 0\}$. For a word $w$ of length
$\ell$ let $R_{\cdot w}$ be the set of natural numbers having a base phi expansion whose digits
$d_{-1} d_{-2} \cdots d_{-\ell}$ spell $w$, where $d_i = 1$ if position $i$ carries a digit $1$
and $d_i = 0$ otherwise. Then for every natural number $N \ge 2$:
$N \in R_{\cdot 0}$ if and only if $N \in V(1, 2, -1) \cup V(1, 2, 0) \cup V(1, 2, 1)$;
$N \in R_{\cdot 1}$ if and only if $N \in V(3, 1, 1)$;
$N \in R_{\cdot 10}$ if and only if $N \in V(3, 1, 1)$;
$N \in R_{\cdot 00}$ if and only if $N \in V(3, 1, 2) \cup V(3, 1, 3) \cup V(3, 1, 4)$;
$N \in R_{\cdot 01}$ if and only if $N \in V_0(4, 3, 2) \cup V_0(4, 3, 3) \cup V_0(4, 3, 4)$;
$N \in R_{\cdot 010}$ if and only if $N \in V_0(4, 3, 2) \cup V_0(4, 3, 3) \cup V_0(4, 3, 4)$;
$N \in R_{\cdot 000}$ if and only if $N \in V(4, 3, -1) \cup V(4, 3, 0) \cup V(4, 3, 1)$;
$N \in R_{\cdot 001}$ if and only if $N \in V(7, 4, 2) \cup V(7, 4, 3) \cup V(7, 4, 4)$;
$N \in R_{\cdot 100}$ if and only if $N \in V(4, 3, -2)$; and
$N \in R_{\cdot 101}$ if and only if $N \in V(7, 4, 1)$.

The bound $N \ge 2$ makes the negative part nonempty: the expansion of $1$ is $1$ itself. The first
equivalence follows the reading $R_{\cdot 0} = V(1, 2, [-1, 0, 1])$ of the paper's Figure 3: as
printed, $V(2, 1, -1) \cup V(2, 1, 0) \cup V(2, 1, 1)$ misses $6$, whose expansion is
$1010 \cdot 0001$, and contains $12$, whose expansion is $100000 \cdot 101001$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Proposition 3 (`integers-2024-A24-prop-3`).
