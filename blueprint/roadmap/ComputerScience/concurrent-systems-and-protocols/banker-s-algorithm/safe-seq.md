# Safe sequence

Let $S$ be a system with processes $P$ and resource types $R$, where
process $p$ has maximum claim $\mathrm{claim}(p)$ and allocation $\mathrm{alloc}(p)$ in
$R \to \mathbb{N}$. A list $p_1, \dots, p_k$ of processes is a safe sequence from the free
resource vector $w : R \to \mathbb{N}$ when, for each $i$, the remaining need
$\mathrm{claim}(p_i) - \mathrm{alloc}(p_i)$ (truncated at zero) is at most
$w + \mathrm{alloc}(p_1) + \cdots + \mathrm{alloc}(p_{i-1})$ componentwise. In particular
the empty list is a safe sequence from every $w$.

Thus each process in turn can be given its remaining need from what is free, finish, and
release its allocation.
