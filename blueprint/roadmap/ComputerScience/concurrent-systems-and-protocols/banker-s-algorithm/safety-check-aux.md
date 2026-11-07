# Banker's safety algorithm with fuel

Let $S$ be a system with processes $P$ and a
finite set $R$ of resource types, where process $p$ has maximum claim $\mathrm{claim}(p)$ and
allocation $\mathrm{alloc}(p)$ in $R \to \mathbb{N}$. Given a fuel $n \in \mathbb{N}$, a free
resource vector $w : R \to \mathbb{N}$ and a list of pending processes, the algorithm succeeds
if the list is empty. Otherwise, if $n > 0$ and some pending process $q$ has remaining need
$\mathrm{claim}(q) - \mathrm{alloc}(q)$ (truncated at zero) at most $w$ componentwise, it takes
the first such process $p$ in the list, removes that occurrence of $p$ from the list, adds
$\mathrm{alloc}(p)$ to $w$ and continues with fuel $n - 1$; if $n = 0$ or no pending process
fits, it fails.
