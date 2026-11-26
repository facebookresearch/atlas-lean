# Transcript of an adaptive composition

Given a family of output types $A_0, A_1, \dots$ indexed by $\mathbb{N}$, the transcript type after $n$ steps is defined by recursion on $n$: after $0$ steps it is the one-point type, and the transcript after $n + 1$ steps is a pair $(t, a)$ of a transcript $t$ after $n$ steps and an output $a \in A_n$. So a transcript after $k$ steps is the nested pair $((\dots((\ast, a_0), a_1), \dots), a_{k-1})$.
