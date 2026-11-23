# Infinite Fibonacci word

Let $f_0 = 0$ and let $f_{k+1}$ be the image of $f_k$ under the
Fibonacci morphism ($0 \mapsto 01$, $1 \mapsto 0$), so that $f_0, f_1, f_2, \ldots$ are the finite
Fibonacci words $0, 01, 010, 01001, \ldots$. The one-sided infinite Fibonacci word is the infinite
binary word whose letter at index $n$ (indices start at $0$) is the letter of $f_{n+2}$ at index
$n$.

Each $f_k$ is a prefix of $f_{k+1}$ and $f_{n+2}$ has more than $n$ letters, so this word is the
limit of the finite Fibonacci words.
