# Blocks of the generalized Thue–Morse sequence

Let $L > 1$ and $k > 1$ be natural numbers,
take the letters $0, 1, \dots, L-1$ (the elements of $\mathbb{Z}/L\mathbb{Z}$), and let $\kappa$
assign a shift $\kappa(j, n) \in \mathbb{Z}/L\mathbb{Z}$ to each $j \in \{1, \dots, k-1\}$ and
each $n \ge 0$. For a word $w$ and $t \in \mathbb{Z}/L\mathbb{Z}$, let $f^t(w)$ be the word
obtained from $w$ by adding $t$ modulo $L$ to every letter. The blocks $A_n$ of the
$(L, k, \kappa)$-Thue–Morse sequence are the words given by $A_0 = 0$ (a word of one letter)
and $A_{n+1} = A_n \, f^{\kappa(1, n)}(A_n) \, f^{\kappa(2, n)}(A_n) \cdots
f^{\kappa(k-1, n)}(A_n)$.
