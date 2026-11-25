# Cloitre's sequence

Let $A_0 = (1, 1)$ and $A_{k+1} = A_k A_k^r$ be the approximants of
Cloitre's sequence, where $A_k^r$ is the mirror image of $A_k$: reverse $A_k$, then replace a
leading $2$ by $1, 1$, or two leading letters $1, 1$ by $2$, and otherwise leave it unchanged.
Cloitre's sequence $s : \mathbb{N} \to \mathbb{N}$ is defined by letting $s(n)$ be the letter at
position $n$ (counting from $0$) of $A_{n+2}$, or $0$ if $A_{n+2}$ has at most $n$ letters.

Each approximant is a prefix of the next and $A_{n+2}$ has more than $n$ letters, so $s$ is the
limit of the approximants. It begins $1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, \ldots$
