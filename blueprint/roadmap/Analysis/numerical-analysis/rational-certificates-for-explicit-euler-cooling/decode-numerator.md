# Decoding a signed numerator

A list of characters that starts with $\texttt{'-'}$ decodes to $-n$ when the rest decodes as a bounded decimal $n$ (one to eleven digits) with $n \le 10^{10}$; a list that does not start with $\texttt{'-'}$ decodes to $n$ under the same conditions. Otherwise the result is none. In particular $\texttt{-0}$ decodes to $0$.
