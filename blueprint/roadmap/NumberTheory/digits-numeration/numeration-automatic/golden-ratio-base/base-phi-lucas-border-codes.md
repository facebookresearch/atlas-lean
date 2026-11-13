# Border words and codes of Lucas numbers

Let $n \ge 1$, and write $F_k$ for the Fibonacci
numbers and $L_k$ for the Lucas numbers. Let $S_1, S_2, S_3, S_4$ be base phi expansions (sets
of positions of the digits $1$) of $L_{2n}$, $L_{2n+1}$, $L_{2n+1} + 1$ and $L_{2n+2} - 1$
respectively, and let $S_k^-$ be the set of negative positions in $S_k$. Then
$S_1^- = \{-2n\}$, $S_2^- = \{-2j : 1 \le j \le n\}$,
$S_3^- = \{-2n-2\} \cup \{1 - 2j : 1 \le j \le n\}$ and $S_4^- = \{-2n-2\}$; that is, the
negative parts $\beta^-$ of these numbers are the words $0^{2n-2}01$, $(01)^n$, $(10)^n 01$ and
$0^{2n}01$. Moreover $\sum_{i \in S_1^-} F_{i+2n} = 0$,
$\sum_{i \in S_2^-} F_{i+2n} = F_{2n-1} - 1$, $\sum_{i \in S_3^-} F_{i+2n+2} = F_{2n+2} - 1$
and $\sum_{i \in S_4^-} F_{i+2n+2} = 0$.

In the paper's notation, with $\gamma^-(N)$ the word $\beta^-(N)$ with its final $01$ removed,
this says $\gamma^-(L_{2n}) = 0^{2n-2}$, $\gamma^-(L_{2n+1}) = (01)^{n-1}$,
$\gamma^-(L_{2n+1}+1) = (10)^n$ and $\gamma^-(L_{2n+2}-1) = 0^{2n}$, and that the codes $C(N)$
of the words $\gamma^-(N)$, which equal $\sum_{i \in \beta^-(N)} F_{i+2j}$ when $\beta^-(N)$
has length $2j$, are $C(L_{2n}) = 0$, $C(L_{2n+1}) = F_{2n-1} - 1$,
$C(L_{2n+1}+1) = F_{2n+2} - 1$ and $C(L_{2n+2}-1) = 0$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Lemma 10.
