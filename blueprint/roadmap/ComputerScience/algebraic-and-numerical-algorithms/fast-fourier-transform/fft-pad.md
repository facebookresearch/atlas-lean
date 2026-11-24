# Zero padding to twice the length

For a type $R$ with a zero, a natural number $d$ and a
vector $x$ of length $2^d$ over $R$, padding returns the vector of length $2^{d+1}$ whose $i$-th
entry is $x_i$ for $i < 2^d$ and $0$ for $2^d \le i < 2^{d+1}$, and charges $3 \cdot 2^d$ time
units.
