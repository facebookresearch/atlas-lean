# Reduction sequences

Let $P$ be a type of processes and $R$ a type of resource types, and
let $S$ be a state that gives each process $p$ an allocation $\mathrm{alloc}(p)$ and a request
$\mathrm{request}(p)$, both functions $R \to \mathbb{N}$ ordered componentwise. A list of
processes $p_1, \dots, p_k$ is a reduction sequence of $S$ from the free vector
$w : R \to \mathbb{N}$ when, for every $1 \le i \le k$, we have
$\mathrm{request}(p_i) \le w + \mathrm{alloc}(p_1) + \dots + \mathrm{alloc}(p_{i-1})$. In
particular the empty list is a reduction sequence from every $w$.

Informally: starting with $w$ free, each process in turn gets its request, finishes, and
releases its allocation.
